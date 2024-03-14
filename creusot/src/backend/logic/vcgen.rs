use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{EarlyBinder, GenericArgsRef, ParamEnv, Ty, TyKind};
use rustc_span::{Span, Symbol};
use why3::{declaration::Signature, ty::Type, Exp, Ident, QName};

use crate::{
    backend::{
        signature::{sig_to_why3, signature_of},
        term::{binop_to_binop, lower_literal, lower_pure},
        ty::{is_int, translate_ty},
        Namer as _, Why3Generator,
    },
    pearlite::{super_visit_term, Literal, Pattern, Term, TermVisitor},
    util::{self, get_builtin},
};

use super::{binders_to_args, CloneMap};

/// Verification conditions for lemma functions.
///
/// As the `let functions` of Why3 leave a lot to be desired and generally cause an impedence
/// mismatch with the rest of Creusot, we have instead implemented a custom VCGen for logic
/// functions.
///
/// This VCGen is a sort of cross between WP and an evaluator, we impose a certain 'evaluation
/// order' on the logical formula so that we can validate the preconditions of function calls and
/// leverage the structure of the lemma function as the proof skeleton.
///
/// There are several intersting / atypical rules here:
///
/// 1. Conjunction: 2. Exists & Forall: 3. Function calls:

struct VCGen<'a, 'tcx> {
    ctx: RefCell<&'a mut Why3Generator<'tcx>>,
    names: RefCell<&'a mut CloneMap<'tcx>>,
    self_id: DefId,
    structurally_recursive: bool,
    param_env: ParamEnv<'tcx>,
}

pub(super) fn vc<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    self_id: DefId,
    t: Term<'tcx>,
    dest: Ident,
    post: Exp,
) -> Result<Exp, VCError<'tcx>> {
    let structurally_recursive = is_structurally_recursive(ctx, self_id, &t);
    VCGen {
        param_env: ctx.param_env(self_id),
        ctx: RefCell::new(ctx),
        names: RefCell::new(names),
        self_id,
        structurally_recursive,
    }
    .build_vc(&t, &|exp| Ok(Exp::let_(dest.clone(), exp, post.clone())))
}

/// Verifies whether a given term is structurally recursive: that is, each recursive call is made to
/// a component of an argument to the prior call.
///
/// The check must also ensure that we are always recursing on the *same* argument since otherwise
/// we could 'ping pong' infinitely.
///
/// Currently, the check is *very* naive: we only consider variables and only check `match`. This
/// means that something like the following would fail:
///
/// ``` match x { Cons(_, tl) => recursive((tl, 0).0) } ```
///
/// This check can be extended in the future
fn is_structurally_recursive(ctx: &mut Why3Generator<'_>, self_id: DefId, t: &Term<'_>) -> bool {
    struct StructuralRecursion {
        smaller_than: HashMap<Symbol, Symbol>,
        self_id: DefId,
        /// Index of the decreasing argument
        decreasing_args: HashSet<Symbol>,

        orig_args: Vec<Symbol>,
    }
    use crate::pearlite::TermKind;

    impl StructuralRecursion {
        fn valid(&self) -> bool {
            self.decreasing_args.len() == 1
        }

        /// Is `t` smaller than the argument `nm`?
        fn is_smaller_than(&self, t: &Term, nm: Symbol) -> bool {
            match &t.kind {
                TermKind::Var(s) => self.smaller_than.get(s) == Some(&nm),
                _ => false,
            }
        }

        // TODO: could make this a `pattern` to term comparison to make it more powerful
        /// Mark `sym` as smaller than `term`. Currently, this only updates the relation if `term` is a variable.
        fn smaller_than(&mut self, sym: Symbol, term: &Term<'_>) {
            let var = match &term.kind {
                TermKind::Var(s) => s,
                _ => return,
            };

            let parent = self.smaller_than.get(var).unwrap_or(var);

            self.smaller_than.insert(sym, *parent);
        }
    }

    impl TermVisitor<'_> for StructuralRecursion {
        fn visit_term(&mut self, term: &Term<'_>) {
            match &term.kind {
                TermKind::Call { id, args, .. } if *id == self.self_id => {
                    for (arg, nm) in args.iter().zip(self.orig_args.iter()) {
                        if self.is_smaller_than(arg, *nm) {
                            self.decreasing_args.insert(*nm);
                        }
                    }
                }
                TermKind::Exists { binder, body } => {
                    let old_smaller = self.smaller_than.clone();
                    self.smaller_than.remove(&binder.0);
                    self.visit_term(body);
                    self.smaller_than = old_smaller;
                }

                TermKind::Forall { binder, body } => {
                    let old_smaller = self.smaller_than.clone();
                    self.smaller_than.remove(&binder.0);
                    self.visit_term(body);
                    self.smaller_than = old_smaller;
                }

                TermKind::Let { pattern, arg, body } => {
                    self.visit_term(arg);
                    let mut binds = Default::default();
                    pattern.binds(&mut binds);
                    let old_smaller = self.smaller_than.clone();
                    self.smaller_than.retain(|nm, _| !binds.contains(&nm));
                    binds.into_iter().for_each(|b| self.smaller_than(b, arg));
                    self.visit_term(body);
                    self.smaller_than = old_smaller;
                }

                TermKind::Match { arms, scrutinee } => {
                    self.visit_term(&scrutinee);

                    for (pat, exp) in arms {
                        let mut binds = Default::default();
                        pat.binds(&mut binds);
                        let old_smaller = self.smaller_than.clone();
                        self.smaller_than.retain(|nm, _| !binds.contains(&nm));
                        binds.into_iter().for_each(|b| self.smaller_than(b, scrutinee));
                        self.visit_term(exp);
                        self.smaller_than = old_smaller;
                    }
                }
                _ => super_visit_term(term, self),
            }
        }
    }

    let orig_args = ctx.sig(self_id).inputs.iter().map(|a| a.0).collect();
    let mut s = StructuralRecursion {
        self_id,
        smaller_than: Default::default(),
        decreasing_args: Default::default(),
        orig_args,
    };

    s.visit_term(&t);

    s.valid()
}

#[derive(Debug)]
pub enum VCError<'tcx> {
    /// `old` doesn't currently make sense inside of a lemma function
    Old(Span),
    /// Too lazy to implement this atm.
    Reborrow(Span),
    /// Same here...
    Closure(Span),
    /// Variants are currently restricted to `Int`
    UnsupportedVariant(Ty<'tcx>, Span),
}

impl<'tcx> VCError<'tcx> {
    pub fn span(&self) -> Span {
        match self {
            VCError::Old(s) => *s,
            VCError::Reborrow(s) => *s,
            VCError::Closure(s) => *s,
            VCError::UnsupportedVariant(_, s) => *s,
        }
    }
}

type PostCont<'a, 'tcx, A> = &'a dyn Fn(A) -> Result<Exp, VCError<'tcx>>;

impl<'a, 'tcx> VCGen<'a, 'tcx> {
    fn lower_literal(&self, lit: &Literal<'tcx>) -> Exp {
        lower_literal(*self.ctx.borrow_mut(), *self.names.borrow_mut(), lit)
    }

    fn lower_pure(&self, lit: &Term<'tcx>) -> Exp {
        lower_pure(*self.ctx.borrow_mut(), *self.names.borrow_mut(), lit)
    }

    fn build_vc(&self, t: &Term<'tcx>, k: PostCont<'_, 'tcx, Exp>) -> Result<Exp, VCError<'tcx>> {
        use crate::pearlite::*;
        match &t.kind {
            // VC(v, Q) = Q(v)
            TermKind::Var(v) => k(Exp::var(util::ident_of(*v))),
            // VC(l, Q) = Q(l)
            TermKind::Lit(l) => k(self.lower_literal(l)),
            // Items are just global names so
            // VC(i, Q) = Q(i)
            TermKind::Item(id, sub) => {
                let item_name =
                    get_func_name(*self.ctx.borrow_mut(), *self.names.borrow_mut(), *id, sub);

                if get_builtin(self.ctx.borrow().tcx, *id).is_some() {
                    // Builtins can leverage Why3 polymorphism and sometimes can cause typeck errors in why3 due to ambiguous type variables so lets fix the type now.
                    k(Exp::qvar(item_name).ascribe(self.ty(t.ty)))
                } else {
                    k(Exp::qvar(item_name))
                }
            }
            // VC(assert { C }, Q) => VC(C, |c| c && Q(()))
            TermKind::Assert { cond } => {
                self.build_vc(cond, &|exp| Ok(exp.lazy_and(k(Exp::Tuple(Vec::new()))?)))
            }
            // VC(f As, Q) = VC(A0, |a0| ... VC(An, |an|
            //  pre(f)(a0..an) /\ variant(f)(a0..an) /\ (post(f)(a0..an, F(a0..an)) -> Q(F a0..an))
            // ))
            TermKind::Call { id, subst, args } => self.build_vc_slice(args, &|args| {
                let tcx = self.ctx.borrow().tcx;
                let pre_sig = EarlyBinder::bind(self.ctx.borrow_mut().sig(*id).clone())
                    .instantiate(tcx, subst);

                let pre_sig = pre_sig.normalize(tcx, self.param_env);
                let arg_subst = pre_sig
                    .inputs
                    .iter()
                    .zip(args.clone())
                    .map(|(nm, res)| (util::ident_of(nm.0), res))
                    .collect();
                let fname =
                    get_func_name(*self.ctx.borrow_mut(), *self.names.borrow_mut(), *id, subst);
                let mut sig =
                    sig_to_why3(*self.ctx.borrow_mut(), *self.names.borrow_mut(), &pre_sig, *id);
                sig.contract.subst(&arg_subst);
                let variant =
                    if *id == self.self_id { self.build_variant(&args)? } else { Exp::mk_true() };

                let call = Exp::qvar(fname).app(args);
                sig.contract.subst(&[("result".into(), call.clone())].into_iter().collect());

                let inner = k(call)?;

                let post = sig
                    .contract
                    .requires_conj()
                    .log_and(variant)
                    .log_and(sig.contract.ensures_conj().implies(inner));

                Ok(post)
            }),

            // VC(A && B, Q) = VC(A, |a| if a then VC(B, Q) else Q(false))
            // VC(A OP B, Q) = VC(A, |a| VC(B, |b| Q(a OP B)))
            TermKind::Binary { op, lhs, rhs } => match op {
                BinOp::And => self.build_vc(lhs, &|lhs| {
                    Ok(Exp::if_(lhs, self.build_vc(rhs, k)?, k(Exp::mk_false())?))
                }),
                // BinOp::Or => self.build_vc(lhs, &|lhs| {
                //     Ok(Exp::if_(lhs, k(Exp::mk_true())?, self.build_vc(rhs, k)?,))
                // }),
                BinOp::Div => self.build_vc(&lhs, &|lhs| {
                    self.build_vc(rhs, &|rhs| k(Exp::var("div").app(vec![lhs.clone(), rhs])))
                }),
                _ => self.build_vc(&lhs, &|lhs| {
                    self.build_vc(rhs, &|rhs| {
                        k(Exp::BinaryOp(binop_to_binop(*op), Box::new(lhs.clone()), Box::new(rhs)))
                    })
                }),
            },
            // VC(OP A, Q) = VC(A |a| Q(OP a))
            TermKind::Unary { op, arg } => self.build_vc(arg, &|arg| {
                let op = match op {
                    UnOp::Not => why3::exp::UnOp::Not,
                    UnOp::Neg => why3::exp::UnOp::Neg,
                };

                k(Exp::UnaryOp(op, Box::new(arg)))
            }),
            // // the dual rule should be the one below but that seems weird...
            // // VC(forall<x> P(x), Q) => (exists<x> VC(P, false)) \/ Q(forall<x>P(x))
            // // Instead, I think the rule should just be the same as for the existential quantifiers?
            TermKind::Forall { binder, body } => {
                let forall_pre = self.build_vc(body, &|_| Ok(Exp::mk_true()))?;
                let ty = self.ty(binder.1);

                let forall_pre = Exp::forall(vec![(binder.0.to_string().into(), ty)], forall_pre);
                let forall_pure = self.lower_pure(t);
                Ok(forall_pre.log_and(k(forall_pure)?))
            }
            // // VC(exists<x> P(x), Q) => (forall<x> VC(P, true)) /\ Q(exists<x>P(x))
            TermKind::Exists { binder, body } => {
                let exists_pre = self.build_vc(body, &|_| Ok(Exp::mk_true()))?;
                let ty = self.ty(binder.1);

                let exists_pre = Exp::forall(vec![(binder.0.to_string().into(), ty)], exists_pre);
                let exists_pure = self.lower_pure(t);
                Ok(exists_pre.log_and(k(exists_pure)?))
            }
            // VC((T...), Q) = VC(T[0], |t0| ... VC(T[N], |tn| Q(t0..tn))))
            TermKind::Tuple { fields } => self.build_vc_slice(fields, &|flds| k(Exp::Tuple(flds))),
            // Same as for tuples
            TermKind::Constructor { typ, variant, fields } => {
                self.build_vc_slice(fields, &|args| {
                    let TyKind::Adt(_, subst) = t.ty.kind() else { unreachable!() };

                    let ctor = self.names.borrow_mut().constructor(
                        self.ctx.borrow().adt_def(typ).variants()[*variant].def_id,
                        subst,
                    );

                    k(Exp::Constructor { ctor, args })
                })
            }
            // VC( * T, Q) = VC(T, |t| Q(*t))
            TermKind::Cur { term } => self.build_vc(&term, &|term| k(Exp::Current(Box::new(term)))),
            // VC( ^ T, Q) = VC(T, |t| Q(^t))
            TermKind::Fin { term } => self.build_vc(&term, &|term| k(Exp::Final(Box::new(term)))),
            // VC(A -> B, Q) = VC(A, VC(B, Q(A -> B)))
            TermKind::Impl { lhs, rhs } => self.build_vc(lhs, &|lhs| {
                Ok(Exp::if_(lhs, self.build_vc(rhs, k)?, k(Exp::mk_true())?))
            }),
            // VC(match A {P -> E}, Q) = VC(A, |a| match a {P -> VC(E, Q)})
            TermKind::Match { scrutinee, arms } => self.build_vc(scrutinee, &|scrut| {
                let arms: Vec<_> = arms
                    .iter()
                    .map(&|arm: &(Pattern<'tcx>, Term<'tcx>)| {
                        Ok((self.build_pattern(&arm.0), self.build_vc(&arm.1, k)?))
                    })
                    .collect::<Result<_, _>>()?;

                Ok(Exp::Match(Box::new(scrut), arms))
            }),
            // VC(let P = A in B, Q) = VC(A, |a| let P = a in VC(B, Q))
            TermKind::Let { pattern, arg, body } => self.build_vc(arg, &|arg| {
                let body = self.build_vc(body, k)?;

                Ok(Exp::Let {
                    pattern: self.build_pattern(pattern),
                    arg: Box::new(arg),
                    body: Box::new(body),
                })
            }),
            // VC(A.f, Q) = VC(A, |a| Q(a.f))
            TermKind::Projection { lhs, name } => {
                let accessor = match lhs.ty.kind() {
                    TyKind::Closure(did, substs) => {
                        self.names.borrow_mut().accessor(*did, substs, 0, *name)
                    }
                    TyKind::Adt(def, substs) => {
                        self.ctx
                            .borrow_mut()
                            .translate_accessor(def.variants()[0u32.into()].fields[*name].did);
                        self.names.borrow_mut().accessor(def.did(), substs, 0, *name)
                    }
                    k => unreachable!("Projection from {k:?}"),
                };

                self.build_vc(lhs, &|lhs| k(Exp::qvar(accessor.clone()).app(vec![lhs])))
            }
            // TODO: lol
            TermKind::Absurd => todo!("absrd"),

            TermKind::Old { .. } => Err(VCError::Old(t.span)),
            TermKind::Closure { .. } => Err(VCError::Closure(t.span)),
            TermKind::Reborrow { .. } => Err(VCError::Reborrow(t.span)),
        }
    }

    fn build_pattern(&self, pat: &Pattern<'tcx>) -> why3::exp::Pattern {
        use why3::exp::Pattern as Pat;
        match pat {
            Pattern::Constructor { adt, variant: _, fields, substs } => {
                let fields = fields.into_iter().map(|pat| self.build_pattern(pat)).collect();
                Pat::ConsP(self.names.borrow_mut().constructor(*adt, substs), fields)
            }
            Pattern::Wildcard => Pat::Wildcard,
            Pattern::Binder(name) => Pat::VarP(name.to_string().into()),
            Pattern::Boolean(b) => {
                if *b {
                    Pat::mk_true()
                } else {
                    Pat::mk_false()
                }
            }
            Pattern::Tuple(pats) => {
                Pat::TupleP(pats.into_iter().map(|pat| self.build_pattern(pat)).collect())
            }
        }
    }

    fn build_vc_slice(
        &self,
        t: &[Term<'tcx>],
        k: PostCont<'_, 'tcx, Vec<Exp>>,
    ) -> Result<Exp, VCError<'tcx>> {
        self.build_vc_slice_inner(t, &|mut args| {
            args.reverse();
            k(args)
        })
    }

    fn build_vc_slice_inner(
        &self,
        t: &[Term<'tcx>],
        k: PostCont<'_, 'tcx, Vec<Exp>>,
    ) -> Result<Exp, VCError<'tcx>> {
        if t.is_empty() {
            k(Vec::new())
        } else {
            self.build_vc(&t[0], &|v| {
                self.build_vc_slice_inner(&t[1..], &|mut vs| {
                    vs.push(v.clone());
                    k(vs)
                })
            })
        }
    }

    fn ty(&self, ty: Ty<'tcx>) -> Type {
        translate_ty(*self.ctx.borrow_mut(), *self.names.borrow_mut(), rustc_span::DUMMY_SP, ty)
    }

    // Generates the expression to test the validity of the variant for a recursive call.
    // Currently restricted to `Int` until we sort out `WellFounded` (soon?)
    //
    // If V is the variant expression at entry and V' is the variant expression of the recursive call it generates
    //  0 <= V && V' < V
    //  Weirdly (to me Xavier) this doesn't check `0 <= V'` but this is actually the same behavior as Why3
    fn build_variant(&self, call_args: &[Exp]) -> Result<Exp, VCError<'tcx>> {
        if self.structurally_recursive {
            return Ok(Exp::mk_true());
        }
        let variant = self.ctx.borrow_mut().sig(self.self_id).contract.variant.clone();
        let Some(variant) = variant else { return Ok(Exp::mk_false()) };

        let top_level_args = self.top_level_args();

        let subst: HashMap<_, _> =
            top_level_args.into_iter().zip(call_args.into_iter().cloned()).collect();
        let orig_variant = self.self_sig().contract.variant.remove(0);
        let mut rec_var_exp = orig_variant.clone();
        rec_var_exp.subst(&subst);
        if is_int(self.ctx.borrow().tcx, variant.ty) {
            Ok(Exp::int(0).leq(orig_variant.clone()).log_and(rec_var_exp.lt(orig_variant)))
        } else {
            Err(VCError::UnsupportedVariant(variant.ty, variant.span))
        }
    }

    fn self_sig(&self) -> Signature {
        signature_of(*self.ctx.borrow_mut(), *self.names.borrow_mut(), self.self_id)
    }

    /// Produces the top-level call expression for the function being verified
    fn top_level_args(&self) -> Vec<Ident> {
        let sig = self.self_sig();
        let (arg_names, _) = binders_to_args(*self.ctx.borrow_mut(), sig.args);
        arg_names
    }
}

// Push into `CloneMap::value`?
pub(crate) fn get_func_name<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> QName {
    let builtin_attr = get_builtin(ctx.tcx, id);

    builtin_attr
        .and_then(|a| {
            // Add dependency
            names.value(id, subst);

            QName::from_string(&a.as_str())
        })
        .map(QName::without_search_path)
        .unwrap_or_else(|| names.value(id, subst))
}
