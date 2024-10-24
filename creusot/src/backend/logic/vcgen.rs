use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use super::{binders_to_args, Dependencies};
use crate::{
    backend::{
        signature::{sig_to_why3, signature_of},
        term::{binop_to_binop, lower_literal, lower_pure},
        ty::{constructor, is_int, translate_ty},
        Namer as _, Why3Generator,
    },
    contracts_items::get_builtin,
    ctx::PreludeModule,
    naming::ident_of,
    pearlite::{super_visit_term, Literal, Pattern, PointerKind, Term, TermVisitor},
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{EarlyBinder, Ty, TyKind, TypingEnv};
use rustc_span::{Span, Symbol};
use why3::{
    declaration::Signature,
    exp::{BinOp, Environment},
    ty::Type,
    Exp, Ident,
};

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
    names: RefCell<&'a mut Dependencies<'tcx>>,
    self_id: DefId,
    structurally_recursive: bool,
    typing_env: TypingEnv<'tcx>,
    subst: RefCell<Environment>,
}

pub(super) fn vc<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    self_id: DefId,
    t: Term<'tcx>,
    dest: Ident,
    post: Exp,
) -> Result<Exp, VCError<'tcx>> {
    let structurally_recursive = is_structurally_recursive(ctx, self_id, &t);
    let bounds = ctx
        .sig(self_id)
        .inputs
        .iter()
        .map(|arg| (arg.0.as_str().into(), Exp::var(arg.0.as_str())))
        .collect();
    let gen = VCGen {
        typing_env: ctx.typing_env(self_id),
        ctx: RefCell::new(ctx),
        names: RefCell::new(names),
        self_id,
        structurally_recursive,
        subst: RefCell::new(Default::default()),
    };
    gen.add_bounds(bounds);
    gen.build_vc(&t, &|exp| Ok(Exp::let_(dest.clone(), exp, post.clone())))
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
                TermKind::Quant { binder, body, .. } => {
                    let old_smaller = self.smaller_than.clone();
                    for name in &binder.0 {
                        self.smaller_than.remove(&name.name);
                    }
                    self.visit_term(body);
                    self.smaller_than = old_smaller;
                }

                TermKind::Let { pattern, arg, body } => {
                    self.visit_term(arg);
                    let mut binds = Default::default();
                    pattern.binds(&mut binds);
                    let old_smaller = self.smaller_than.clone();
                    self.smaller_than.retain(|nm, _| !binds.contains(nm));
                    binds.into_iter().for_each(|b| self.smaller_than(b, arg));
                    self.visit_term(body);
                    self.smaller_than = old_smaller;
                }

                TermKind::Match { arms, scrutinee } => {
                    self.visit_term(scrutinee);

                    for (pat, exp) in arms {
                        let mut binds = Default::default();
                        pat.binds(&mut binds);
                        let old_smaller = self.smaller_than.clone();
                        self.smaller_than.retain(|nm, _| !binds.contains(nm));
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

    s.visit_term(t);

    s.valid()
}

#[derive(Debug)]
pub enum VCError<'tcx> {
    /// `old` doesn't currently make sense inside of a lemma function
    OldInLemma(Span),
    /// Too lazy to implement this atm.
    UnimplementedReborrow(Span),
    /// Same here...
    UnimplementedClosure(Span),
    /// Variants are currently restricted to `Int`
    #[allow(dead_code)] // this lint is too agressive
    UnsupportedVariant(Ty<'tcx>, Span),
}

impl<'tcx> VCError<'tcx> {
    pub fn span(&self) -> Span {
        match self {
            VCError::OldInLemma(s) => *s,
            VCError::UnimplementedReborrow(s) => *s,
            VCError::UnimplementedClosure(s) => *s,
            VCError::UnsupportedVariant(_, s) => *s,
        }
    }
}

type PostCont<'a, 'tcx, A, R = Exp> = &'a dyn Fn(A) -> Result<R, VCError<'tcx>>;

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
            TermKind::Var(v) => {
                let id = ident_of(*v);
                let exp = self.subst.borrow().get(&id).unwrap_or(Exp::var(id));
                k(exp)
            }
            // VC(l, Q) = Q(l)
            TermKind::Lit(l) => k(self.lower_literal(l)),
            // Items are just global names so
            // VC(i, Q) = Q(i)
            TermKind::Item(id, sub) => {
                let item_name = self.names.borrow_mut().value(*id, sub);

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

                let pre_sig = pre_sig.normalize(tcx, self.typing_env);
                let arg_subst = pre_sig
                    .inputs
                    .iter()
                    .zip(args.clone())
                    .map(|(nm, res)| (ident_of(nm.0), res))
                    .collect();
                let fname = self.names.borrow_mut().value(*id, subst);
                let mut sig = sig_to_why3(
                    *self.ctx.borrow_mut(),
                    *self.names.borrow_mut(),
                    "".into(),
                    pre_sig,
                    *id,
                );
                sig.contract.subst(&arg_subst);
                let variant =
                    if *id == self.self_id { self.build_variant(&args)? } else { Exp::mk_true() };

                let call = if args.is_empty() {
                    Exp::qvar(fname).app_to(Exp::Tuple(Vec::new()))
                } else {
                    Exp::qvar(fname).app(args)
                };
                sig.contract.subst(&[("result".into(), call.clone())].into_iter().collect());

                let inner = k(call)?;

                let post = sig
                    .contract
                    .requires_conj_labelled()
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
                BinOp::Div => self.build_vc(lhs, &|lhs| {
                    self.build_vc(rhs, &|rhs| k(Exp::var("div").app(vec![lhs.clone(), rhs])))
                }),
                _ => self.build_vc(lhs, &|lhs| {
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
            TermKind::Quant { kind: QuantKind::Forall, binder, body, .. } => {
                let forall_pre = self.build_vc(body, &|_| Ok(Exp::mk_true()))?;

                let forall_pre = Exp::forall(
                    zip_binder(binder).map(|(s, t)| (s.to_string().into(), self.ty(t))).collect(),
                    forall_pre,
                );
                let forall_pure = self.lower_pure(t);
                Ok(forall_pre.log_and(k(forall_pure)?))
            }
            // // VC(exists<x> P(x), Q) => (forall<x> VC(P, true)) /\ Q(exists<x>P(x))
            TermKind::Quant { kind: QuantKind::Exists, binder, body, .. } => {
                let exists_pre = self.build_vc(body, &|_| Ok(Exp::mk_true()))?;

                let exists_pre = Exp::forall(
                    zip_binder(binder).map(|(s, t)| (s.to_string().into(), self.ty(t))).collect(),
                    exists_pre,
                );
                let exists_pure = self.lower_pure(t);
                Ok(exists_pre.log_and(k(exists_pure)?))
            }
            // VC((T...), Q) = VC(T[0], |t0| ... VC(T[N], |tn| Q(t0..tn))))
            TermKind::Tuple { fields } => self.build_vc_slice(fields, &|flds| k(Exp::Tuple(flds))),
            // Same as for tuples
            TermKind::Constructor { variant, fields, .. } => {
                let ty =
                    self.ctx.borrow().normalize_erasing_regions(self.typing_env, t.creusot_ty());
                let TyKind::Adt(adt, subst) = ty.kind() else { unreachable!() };
                self.build_vc_slice(fields, &|fields| {
                    let ctor = constructor(
                        *self.names.borrow_mut(),
                        fields,
                        adt.variant(*variant).def_id,
                        subst,
                    );
                    k(ctor)
                })
            }
            // VC( * T, Q) = VC(T, |t| Q(*t))
            TermKind::Cur { term } => self.build_vc(term, &|term| k(term.field("current"))),
            // VC( ^ T, Q) = VC(T, |t| Q(^t))
            TermKind::Fin { term } => self.build_vc(term, &|term| k(term.field("final"))),
            // VC(A -> B, Q) = VC(A, VC(B, Q(A -> B)))
            TermKind::Impl { lhs, rhs } => self.build_vc(lhs, &|lhs| {
                Ok(Exp::if_(lhs, self.build_vc(rhs, k)?, k(Exp::mk_true())?))
            }),
            // VC(match A {P -> E}, Q) = VC(A, |a| match a {P -> VC(E, Q)})
            TermKind::Match { scrutinee, arms }
                if scrutinee.ty.is_bool()
                    && arms.len() == 2
                    && arms.iter().all(|a| a.0.get_bool().is_some()) =>
            {
                self.build_vc(scrutinee, &|scrut| {
                    let mut arms: Vec<_> = arms
                        .iter()
                        .map(&|arm: &(Pattern<'tcx>, Term<'tcx>)| {
                            Ok((arm.0.get_bool().unwrap(), self.build_vc(&arm.1, k)?))
                        })
                        .collect::<Result<_, _>>()?;
                    arms.sort_by(|a, b| b.0.cmp(&a.0));

                    Ok(Exp::if_(scrut, arms.remove(0).1, arms.remove(0).1))
                })
            }

            // VC(match A {P -> E}, Q) = VC(A, |a| match a {P -> VC(E, Q)})
            TermKind::Match { scrutinee, arms } => self.build_vc(scrutinee, &|scrut| {
                let arms: Vec<_> = arms
                    .iter()
                    .map(&|arm: &(Pattern<'tcx>, Term<'tcx>)| {
                        self.build_pattern(&arm.0, &|pat| Ok((pat, self.build_vc(&arm.1, k)?)))
                    })
                    .collect::<Result<_, _>>()?;

                Ok(Exp::Match(Box::new(scrut), arms))
            }),
            // VC(let P = A in B, Q) = VC(A, |a| let P = a in VC(B, Q))
            TermKind::Let { pattern, arg, body } => self.build_vc(arg, &|arg| {
                self.build_pattern(pattern, &|pattern| {
                    let body = self.build_vc(body, k)?;

                    Ok(Exp::Let { pattern, arg: Box::new(arg.clone()), body: Box::new(body) })
                })
            }),
            // VC(A.f, Q) = VC(A, |a| Q(a.f))
            TermKind::Projection { lhs, name } => {
                let ty =
                    self.ctx.borrow().normalize_erasing_regions(self.typing_env, lhs.creusot_ty());
                let field = match ty.kind() {
                    TyKind::Closure(did, substs) => {
                        self.names.borrow_mut().field(*did, substs, *name).as_ident()
                    }
                    TyKind::Adt(def, substs) => {
                        self.names.borrow_mut().field(def.did(), substs, *name).as_ident()
                    }
                    TyKind::Tuple(f) => {
                        let mut fields = vec![why3::exp::Pattern::Wildcard; f.len()];
                        fields[name.as_usize()] = why3::exp::Pattern::VarP("a".into());

                        return self.build_vc(lhs, &|lhs| {
                            k(Exp::Let {
                                pattern: why3::exp::Pattern::TupleP(fields.clone()),
                                arg: Box::new(lhs),
                                body: Box::new(Exp::var("a")),
                            })
                        });
                    }
                    k => unreachable!("Projection from {k:?}"),
                };

                self.build_vc(lhs, &|lhs| k(lhs.field(&field)))
            }
            TermKind::Old { .. } => Err(VCError::OldInLemma(t.span)),
            TermKind::Closure { .. } => Err(VCError::UnimplementedClosure(t.span)),
            TermKind::Reborrow { .. } => Err(VCError::UnimplementedReborrow(t.span)),
            TermKind::Precondition { .. } => Err(VCError::UnimplementedClosure(t.span)),
            TermKind::Postcondition { .. } => Err(VCError::UnimplementedClosure(t.span)),
        }
    }

    fn build_pattern<A>(
        &self,
        pat: &Pattern<'tcx>,
        k: PostCont<'_, 'tcx, why3::exp::Pattern, A>,
    ) -> Result<A, VCError<'tcx>> {
        let mut bounds = Default::default();
        let pat = self.build_pattern_inner(&mut bounds, pat);
        self.add_bounds(bounds);
        // FIXME: this totally breaks the tail-call potential... which needs desparate fixing.
        let r = k(pat);
        self.pop_bounds();
        r
    }

    fn build_pattern_inner(
        &self,
        bounds: &mut HashMap<Ident, Exp>,
        pat: &Pattern<'tcx>,
    ) -> why3::exp::Pattern {
        use why3::exp::Pattern as Pat;
        match pat {
            Pattern::Constructor { variant, fields, substs } => {
                let fields =
                    fields.iter().map(|pat| self.build_pattern_inner(bounds, pat)).collect();
                let substs = self.ctx.borrow().normalize_erasing_regions(self.typing_env, *substs);
                if self.ctx.borrow().def_kind(variant) == DefKind::Variant {
                    Pat::ConsP(self.names.borrow_mut().constructor(*variant, substs), fields)
                } else if fields.is_empty() {
                    Pat::TupleP(vec![])
                } else {
                    Pat::RecP(
                        fields
                            .into_iter()
                            .enumerate()
                            .map(|(i, f)| {
                                (
                                    self.names
                                        .borrow_mut()
                                        .field(*variant, substs, i.into())
                                        .as_ident(),
                                    f,
                                )
                            })
                            .filter(|(_, f)| !matches!(f, Pat::Wildcard))
                            .collect(),
                    )
                }
            }
            Pattern::Wildcard => Pat::Wildcard,
            Pattern::Binder(name) => {
                let name_id = name.as_str().into();
                let new = self.uniq_occ(&name_id);
                bounds.insert(name_id, Exp::var(new.clone()));
                Pat::VarP(new)
            }
            Pattern::Boolean(b) => {
                if *b {
                    Pat::mk_true()
                } else {
                    Pat::mk_false()
                }
            }
            Pattern::Tuple(pats) => {
                Pat::TupleP(pats.iter().map(|pat| self.build_pattern_inner(bounds, pat)).collect())
            }
            Pattern::Deref { pointee, kind } => match kind {
                PointerKind::Box | PointerKind::Shr => self.build_pattern_inner(bounds, pointee),
                PointerKind::Mut => {
                    Pat::RecP(vec![("current".into(), self.build_pattern_inner(bounds, pointee))])
                }
            },
        }
    }

    fn uniq_occ(&self, id: &Ident) -> Ident {
        let occ = self.subst.borrow().occ(id);

        if occ == 0 {
            id.clone()
        } else {
            Ident::from_string(format!("{}_{occ}", &**id))
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

    fn self_sig(&self) -> Signature {
        signature_of(*self.ctx.borrow_mut(), *self.names.borrow_mut(), "".into(), self.self_id)
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

        let mut subst: Environment =
            top_level_args.into_iter().zip(call_args.iter().cloned()).collect();
        let orig_variant = self.self_sig().contract.variant.remove(0);
        let mut rec_var_exp = orig_variant.clone();
        rec_var_exp.subst(&mut subst);
        if is_int(self.ctx.borrow().tcx, variant.creusot_ty()) {
            self.names.borrow_mut().import_prelude_module(PreludeModule::Int);
            Ok(Exp::BinaryOp(BinOp::Le, Box::new(Exp::int(0)), Box::new(orig_variant.clone()))
                .log_and(Exp::BinaryOp(BinOp::Lt, Box::new(rec_var_exp), Box::new(orig_variant))))
        } else {
            Err(VCError::UnsupportedVariant(variant.creusot_ty(), variant.span))
        }
    }

    /// Produces the top-level call expression for the function being verified
    fn top_level_args(&self) -> Vec<Ident> {
        let sig = self.self_sig();
        let (arg_names, _) = binders_to_args(sig.args);
        arg_names
    }

    fn add_bounds(&self, bounds: HashMap<Ident, Exp>) {
        self.subst.borrow_mut().add_subst(bounds);
    }

    fn pop_bounds(&self) {
        self.subst.borrow_mut().pop_subst();
    }
}
