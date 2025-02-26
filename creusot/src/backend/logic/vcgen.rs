use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use super::Dependencies;
use crate::{
    backend::{
        signature::sig_to_why3,
        term::{binop_to_binop, lower_literal, lower_pure},
        ty::{constructor, ity_to_prelude, translate_ty, uty_to_prelude},
        Namer as _, Why3Generator,
    },
    contracts_items::get_builtin,
    ctx::PreludeModule,
    pearlite::{super_visit_term, Literal, Pattern, PointerKind, Term, TermVisitor},
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{EarlyBinder, Ty, TyKind, TypingEnv};
use rustc_span::Span;
use why3::{
    exp::Environment,
    ty::Type,
    Exp, Ident,
};
use crate::pearlite::Renaming;

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
    ctx: &'a Why3Generator<'tcx>,
    names: &'a Dependencies<'tcx>,
    self_id: DefId,
    structurally_recursive: bool,
    variant: Option<Exp>,
    typing_env: TypingEnv<'tcx>,
    renaming: RefCell<Renaming>,
}

pub(super) fn vc<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    self_id: DefId,
    t: Term<'tcx>,
    dest: Ident,
    post: Exp,
) -> Result<Exp, VCError<'tcx>> {
    let structurally_recursive = is_structurally_recursive(ctx, self_id, &t);
    let sig = ctx.sig(self_id);
    let bounds = todo!{}; /* TODO REMOVE THIS sig
        .inputs
        .iter()
        .map(|(sym, _, _)| (*sym, Ident::fresh(sym.as_str())))
        .collect(); */
    let renaming = RefCell::new(bounds);
    let variant = sig.contract.variant.as_ref().map(|term|
            lower_pure(ctx, names, &renaming, term));
    let gen = VCGen {
        typing_env: ctx.typing_env(self_id),
        ctx,
        names,
        self_id,
        structurally_recursive,
        variant,
        renaming,
    };
    let hole = Ident::fresh("");
    let exp = Exp::let_(dest.clone(), Exp::Var(hole), post.clone());
    gen.build_vc(&t, &mut Post::new(exp, hole))
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
fn is_structurally_recursive(ctx: &Why3Generator<'_>, self_id: DefId, t: &Term<'_>) -> bool {
    struct StructuralRecursion {
        smaller_than: HashMap<why3::Ident, why3::Ident>,
        self_id: DefId,
        /// Index of the decreasing argument
        decreasing_args: HashSet<why3::Ident>,

        orig_args: Vec<why3::Ident>,
    }
    use crate::pearlite::TermKind;

    impl StructuralRecursion {
        fn valid(&self) -> bool {
            self.decreasing_args.len() == 1
        }

        /// Is `t` smaller than the argument `nm`?
        fn is_smaller_than(&self, t: &Term, nm: why3::Ident) -> bool {
            match &t.kind {
                TermKind::Var(s) => self.smaller_than.get(s) == Some(&nm),
                _ => false,
            }
        }

        // TODO: could make this a `pattern` to term comparison to make it more powerful
        /// Mark `sym` as smaller than `term`. Currently, this only updates the relation if `term` is a variable.
        fn smaller_than(&mut self, sym: why3::Ident, term: &Term<'_>) {
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
                    for (name, _) in binder {
                        self.smaller_than.remove(name);
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

struct Post {
    exp: Exp,
    substs: Vec<(Ident, Exp)>,
    hole: Ident,
}

impl Post {
    fn new(exp: Exp, hole: Ident) -> Self {
        Self { exp, substs: Vec::new(), hole }
    }

    fn subst(&mut self, exp: Exp) {
        self.substs.push((self.hole, exp));
    }

    fn undo_subst(&mut self) {
        if let Some((hole, _)) = self.substs.pop() {
            self.hole = hole;
        } else {
            panic!("No subst to undo");
        }
    }

    fn subst_to_exp(&self, exp: Exp) -> Exp {
        let mut env = Environment::new();
        env.add_subst(std::iter::once((self.hole, exp.clone())).collect());
        for (h, e) in self.substs.iter().rev() {
            let mut e = e.clone();
            e.subst(&mut env);
            env.add_subst(std::iter::once((*h,e.clone())).collect());
        }
        let mut exp = self.exp.clone();
        exp.subst(&mut env);
        exp
    }
}

impl<'a, 'tcx> VCGen<'a, 'tcx> {
    fn lower_literal(&self, lit: &Literal<'tcx>) -> Exp {
        lower_literal(self.ctx, self.names, lit)
    }

    fn lower_pure(&self, lit: &Term<'tcx>) -> Exp {
        lower_pure(self.ctx, self.names, &self.renaming, lit)
    }

    fn build_vc(&self, t: &Term<'tcx>, q: &mut Post) -> Result<Exp, VCError<'tcx>> {
        use crate::pearlite::*;
        match &t.kind {
            // VC(v, Q) = Q(v)
            TermKind::Var(v) => Ok(q.subst_to_exp(Exp::Var(self.get_var(*v).expect(&format!{"Unbound {:?} in {:?}", v, self.ctx.current})))),
            // VC(l, Q) = Q(l)
            TermKind::Lit(l) => Ok(q.subst_to_exp(self.lower_literal(l))),
            // VC(cast(arg), Q) = VC(arg, |a| Q(cast(a)))
            TermKind::Cast { arg } => match arg.ty.kind() {
                TyKind::Bool => {
                    let (fct_name, prelude_kind) = match t.ty.kind() {
                        TyKind::Int(ity) => ("of_bool", ity_to_prelude(self.ctx.tcx, *ity)),
                        TyKind::Uint(uty) => ("of_bool", uty_to_prelude(self.ctx.tcx, *uty)),
                        _ => self.ctx.crash_and_error(
                            t.span,
                            "bool cast to non integral casts are currently unsupported",
                        ),
                    };

                    let qname = self.names.from_prelude(prelude_kind, fct_name);
                    q.subst(Exp::Call(Box::new(Exp::qvar(qname)), vec![Exp::Var(q.hole)]));
                    let vc = self.build_vc(arg, q)?;
                    q.undo_subst();
                    Ok(vc)
                },
                TyKind::Int(_) | TyKind::Uint(_) => {
                    // to
                    let to_fct_name = if self.names.bitwise_mode() { "to_BV256" } else { "to_int" };
                    let to_prelude = match arg.ty.kind() {
                        TyKind::Int(ity) => ity_to_prelude(self.ctx.tcx, *ity),
                        TyKind::Uint(ity) => uty_to_prelude(self.ctx.tcx, *ity),
                        _ => self.ctx.crash_and_error(
                            t.span,
                            &format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    // of
                    let of_fct_name = if self.names.bitwise_mode() { "of_BV256" } else { "of_int" };
                    let of_prelude = match t.ty.kind() {
                        TyKind::Int(ity) => ity_to_prelude(self.ctx.tcx, *ity),
                        TyKind::Uint(ity) => uty_to_prelude(self.ctx.tcx, *ity),
                        _ => self.ctx.crash_and_error(
                            t.span,
                            &format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    let to_qname = self.names.from_prelude(to_prelude, to_fct_name);
                    let of_qname = self.names.from_prelude(of_prelude, of_fct_name);
                    q.subst(Exp::qvar(of_qname).app(vec![Exp::qvar(to_qname).app(vec![Exp::Var(q.hole)])]));
                    let vc = self.build_vc(arg, q)?;
                    q.undo_subst();
                    Ok(vc)
                }
                _ => self.ctx.crash_and_error(
                    t.span,
                    "casting from a type that is not a boolean is not supported",
                ),
            },
            // Items are just global names so
            // VC(i, Q) = Q(i)
            TermKind::Item(id, sub) => {
                let item_name = self.names.item(*id, sub);
                if get_builtin(self.ctx.tcx, *id).is_some() {
                    // Builtins can leverage Why3 polymorphism and sometimes can cause typeck errors in why3 due to ambiguous type variables so lets fix the type now.
                    Ok(q.subst_to_exp(Exp::qvar(item_name).ascribe(self.ty(t.ty))))
                } else {
                    Ok(q.subst_to_exp(Exp::qvar(item_name)))
                }
            }
            // VC(assert { C }, Q) => VC(C, |c| c && Q(()))
            TermKind::Assert { cond } => {
                let hole = q.hole;
                let exp = Exp::Var(hole).lazy_and(q.subst_to_exp(Exp::Tuple(Vec::new())));
                self.build_vc(cond, &mut Post::new(exp, hole))
            }
            // VC(f As, Q) = VC(A0, |a0| ... VC(An, |an|
            //  pre(f)(a0..an) /\ variant(f)(a0..an) /\ (post(f)(a0..an, F(a0..an)) -> Q(F a0..an))
            // ))
            TermKind::Call { id, subst, args } => {
                let args: Vec<_> = args.into_iter().map(|arg| (arg, Ident::fresh(""))).collect();
                let pre_sig =
                    EarlyBinder::bind(self.ctx.sig(*id).clone()).instantiate(self.ctx.tcx, subst);

                let pre_sig = pre_sig.normalize(self.ctx.tcx, self.typing_env);
                let sig =  sig_to_why3(self.ctx, self.names, Ident::fresh(""), // ???
                    pre_sig, *id);
                let arg_subst = sig
                    .args
                    .iter()
                    .zip(&args)
                    .map(|(&(arg, _), &(_, hole))| (arg, Exp::Var(hole)))
                    .collect();
                let mut contract = sig.contract;
                contract.subst(&arg_subst);
                // Generates the expression to test the validity of the variant for a recursive call.
                // Currently restricted to `Int` until we sort out `WellFounded` (soon?)
                //
                // If V is the variant expression at entry and V' is the variant expression of the recursive call it generates
                //  0 <= V && V' < V
                //  Weirdly (to me Xavier) this doesn't check `0 <= V'` but this is actually the same behavior as Why3
                let variant = if *id == self.self_id && !self.structurally_recursive {
                    let variant = contract.variant.remove(0);
                    let orig_variant = self.variant.clone().unwrap();
                    self.names.import_prelude_module(PreludeModule::Int);
                    Exp::BinaryOp(why3::exp::BinOp::Le, Box::new(Exp::int(0)), Box::new(orig_variant.clone()))
                        .log_and(Exp::BinaryOp(why3::exp::BinOp::Lt, Box::new(variant), Box::new(orig_variant)))
                    /* TODO: check type is int when translating the variant Err(VCError::UnsupportedVariant(variant.creusot_ty(), variant.span)); */
                } else { Exp::mk_true() };

                let fname = self.names.item(*id, subst);
                let call = if args.is_empty() {
                    Exp::qvar(fname).app_to(Exp::unit())
                } else {
                    Exp::qvar(fname).app(args.iter().map(|(_, arg)| Exp::Var(*arg)).collect())
                };
                contract.subst(&[(Ident::bound("result"), call.clone())].into_iter().collect());

                let inner = q.subst_to_exp(call);

                let post = contract
                    .requires_conj_labelled()
                    .log_and(variant)
                    .log_and(contract.ensures_conj().implies(inner));

                self.build_vc_slice(&args, post)
            }

            // VC(A && B, Q) = VC(A, |a| if a then VC(B, Q) else Q(false))
            // VC(A || B, Q) = VC(A, |a| if a then Q(true) else VC(B, Q))
            // VC(A OP B, Q) = VC(A, |a| VC(B, |b| Q(a OP B)))
            TermKind::Binary { op, lhs, rhs } => match op {
                BinOp::And => {
                    let vc_rhs = self.build_vc(rhs, q)?;
                    let exp = Exp::if_(Exp::Var(q.hole), vc_rhs, q.subst_to_exp(Exp::mk_false()));
                    self.build_vc(lhs, &mut Post::new(exp, q.hole))
                }
                BinOp::Or => {
                    let vc_rhs = self.build_vc(rhs, q)?;
                    let exp = Exp::if_(Exp::Var(q.hole), q.subst_to_exp(Exp::mk_true()), vc_rhs);
                    self.build_vc(lhs, &mut Post::new(exp, q.hole))
                }
                BinOp::Div => {
                    let lhs_hole = Ident::fresh("");
                    q.subst(Exp::QVar("div".into()).app(vec![Exp::Var(lhs_hole), Exp::Var(q.hole)]));
                    let vc_rhs = self.build_vc(rhs, q)?;
                    q.undo_subst();
                    self.build_vc(lhs, &mut Post::new(vc_rhs, lhs_hole))
                }
                BinOp::Rem => {
                    let lhs_hole = Ident::fresh("");
                    q.subst(Exp::QVar("mod".into()).app(vec![Exp::Var(lhs_hole), Exp::Var(q.hole)]));
                    let vc_rhs = self.build_vc(rhs, q)?;
                    q.undo_subst();
                    self.build_vc(lhs, &mut Post::new(vc_rhs, lhs_hole))
                }
                _ => {
                    let lhs_hole = Ident::fresh("");
                    q.subst(Exp::BinaryOp(binop_to_binop(*op), Exp::Var(lhs_hole).into(), Exp::Var(q.hole).into()));
                    let vc_rhs = self.build_vc(rhs, q)?;
                    q.undo_subst();
                    self.build_vc(lhs, &mut Post::new(vc_rhs, lhs_hole))
                }
            },
            // VC(OP A, Q) = VC(A, |a| Q(OP a))
            TermKind::Unary { op, arg } => {
                let op = match op {
                    UnOp::Not => why3::exp::UnOp::Not,
                    UnOp::Neg => why3::exp::UnOp::Neg,
                };
                q.subst(Exp::UnaryOp(op, Exp::Var(q.hole).into()));
                let vc = self.build_vc(arg, q);
                q.undo_subst();
                vc
            }
            // VC(QUANTIFIER<x> P(x), Q) => (forall<x> VC(P, true)) /\ Q(QUANTIFIER<x> P(x))
            TermKind::Quant { binder, body, .. } => {
                self.open_scope();
                let binder = binder.iter().map(|(ident, ty)| (*ident, self.ty(*ty))).collect();
                let forall_pre = self.build_vc(body, &mut Post::new(Exp::mk_true(), q.hole))?;
                self.close_scope();
                let forall_pre = Exp::forall(binder, forall_pre);
                let q_t = q.subst_to_exp(self.lower_pure(t));
                Ok(forall_pre.log_and(q_t))
            }
            // VC((T...), Q) = VC(T[0], |t0| ... VC(T[N], |tn| Q(t0..tn))))
            TermKind::Tuple { fields } => {
                let fields: Vec<_> = fields.iter().map(|field| (field, Ident::fresh(""))).collect();
                let post = q.subst_to_exp(Exp::Tuple(fields.iter().map(|&(_, v)| Exp::Var(v)).collect()));
                self.build_vc_slice(&fields, post)
            }
            // Same as for tuples
            TermKind::Constructor { variant, fields, .. } => {
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, t.creusot_ty());
                let TyKind::Adt(adt, subst) = ty.kind() else { unreachable!() };
                let fields: Vec<_> = fields.iter().map(|field| (field, Ident::fresh(""))).collect();
                let post = q.subst_to_exp(constructor(self.names, fields.iter().map(|&(_, v)| Exp::Var(v)).collect(), adt.variant(*variant).def_id, subst));
                self.build_vc_slice(&fields, post)
            }
            // VC( * T, Q) = VC(T, |t| Q(*t))
            TermKind::Cur { term } => {
                q.subst(Exp::Var(q.hole).field("current"));
                let vc = self.build_vc(term, q)?;
                q.undo_subst();
                Ok(vc)
            }
            // VC( ^ T, Q) = VC(T, |t| Q(^t))
            TermKind::Fin { term } => {
                q.subst(Exp::Var(q.hole).field("final"));
                let vc = self.build_vc(term, q)?;
                q.undo_subst();
                Ok(vc)
            }
            // VC(A -> B, Q) = VC(A, |a| if a then VC(B, |b| Q(b)) else true)
            TermKind::Impl { lhs, rhs } => {
                let vc_b = self.build_vc(rhs, q)?;
                let exp = Exp::if_(Exp::Var(q.hole), vc_b, Exp::mk_true());
                self.build_vc(lhs, &mut Post::new(exp, q.hole))
            }
            // VC(match A {P -> E}, Q) = VC(A, |a| match a {P -> VC(E, Q)})
            TermKind::Match { scrutinee, arms }
                if scrutinee.ty.is_bool()
                    && arms.len() == 2
                    && arms.iter().all(|a| a.0.get_bool().is_some()) =>
            {
                let mut arms: Vec<_> = arms
                    .iter()
                    .map(|arm: &(Pattern<'tcx>, Term<'tcx>)| {
                        Ok((arm.0.get_bool().unwrap(), self.build_vc(&arm.1, q)?))
                    })
                    .collect::<Result<_, _>>()?;
                arms.sort_by(|a, b| b.0.cmp(&a.0));
                let exp = Exp::if_(Exp::Var(q.hole), arms.remove(0).1, arms.remove(0).1);
                self.build_vc(scrutinee, &mut Post::new(exp, q.hole))
            }
            // VC(match A {P -> E}, Q) = VC(A, |a| match a {P -> VC(E, Q)})
            TermKind::Match { scrutinee, arms } => {
                let arms: Vec<_> = arms
                    .iter()
                    .map(|arm: &(Pattern<'tcx>, Term<'tcx>)| {
                        self.open_scope();
                        let pat = self.build_pattern(&arm.0);
                        let vc = self.build_vc(&arm.1, q)?;
                        self.close_scope();
                        Ok((pat, vc))
                    })
                    .collect::<Result<_, _>>()?;
                let exp = Exp::Match(Box::new(Exp::Var(q.hole)), arms);
                self.build_vc(scrutinee, &mut Post::new(exp, q.hole))
            }
            // VC(let P = A in B, Q) = VC(A, |a| let P = a in VC(B, Q))
            TermKind::Let { pattern, arg, body } => {
                self.open_scope();
                let pattern = self.build_pattern(pattern);
                let body = self.build_vc(body, q)?;
                self.close_scope();
                let exp = Exp::Let { pattern, arg: Box::new(Exp::Var(q.hole)), body: Box::new(body) };
                self.build_vc(arg, &mut Post::new(exp, q.hole))
            }
            // VC(A.f, Q) = VC(A, |a| Q(a.f))
            TermKind::Projection { lhs, name } => {
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, lhs.creusot_ty());
                let field = match ty.kind() {
                    TyKind::Closure(did, substs) => {
                        let field = self.names.field(*did, substs, *name);
                        Exp::Var(q.hole).field(&field.as_str())
                    }
                    TyKind::Adt(def, substs) => {
                        let field = self.names.field(def.did(), substs, *name);
                        Exp::Var(q.hole).field(&field.as_str())
                    }
                    TyKind::Tuple(f) => {
                        let mut fields = vec![why3::exp::Pattern::Wildcard; f.len()];
                        let a = Ident::fresh("a");
                        fields[name.as_usize()] = why3::exp::Pattern::VarP(a);
                        Exp::Let {
                                pattern: why3::exp::Pattern::TupleP(fields.clone()),
                                arg: Box::new(Exp::Var(q.hole)),
                                body: Box::new(Exp::Var(a)),
                            }
                    }
                    k => unreachable!("Projection from {k:?}"),
                };
                q.subst(field);
                let vc = self.build_vc(lhs, q)?;
                q.undo_subst();
                Ok(vc)
            }
            TermKind::Old { .. } => Err(VCError::OldInLemma(t.span)),
            TermKind::Closure { .. } => Err(VCError::UnimplementedClosure(t.span)),
            TermKind::Reborrow { .. } => Err(VCError::UnimplementedReborrow(t.span)),
            TermKind::Precondition { .. } => Err(VCError::UnimplementedClosure(t.span)),
            TermKind::Postcondition { .. } => Err(VCError::UnimplementedClosure(t.span)),
        }
    }

    fn build_pattern(
        &self,
        pat: &Pattern<'tcx>,
    ) -> why3::exp::Pattern {
        use why3::exp::Pattern as Pat;
        match pat {
            Pattern::Constructor { variant, fields, substs } => {
                let fields =
                    fields.iter().map(|pat| self.build_pattern(pat)).collect();
                let substs = self.ctx.normalize_erasing_regions(self.typing_env, *substs);
                if self.ctx.def_kind(variant) == DefKind::Variant {
                    Pat::ConsP(self.names.constructor(*variant, substs), fields)
                } else if fields.is_empty() {
                    Pat::TupleP(vec![])
                } else {
                    Pat::RecP(

                                    fields
                            .into_iter()
                            .enumerate()
                            .map(|(i, f)| {
                                (Ident::bound(self.names.field(*variant, substs, i.into()).as_str()), f)
                            })
                            .filter(|(_, f)| !matches!(f, Pat::Wildcard))
                            .collect(),
                    )
                }
            }
            Pattern::Wildcard => Pat::Wildcard,
            Pattern::Binder(name) => Pat::VarP(self.fresh(*name)),
            Pattern::Boolean(b) => {
                if *b {
                    Pat::mk_true()
                } else {
                    Pat::mk_false()
                }
            }
            Pattern::Tuple(pats) => {
                Pat::TupleP(pats.iter().map(|pat| self.build_pattern(pat)).collect())
            }
            Pattern::Deref { pointee, kind } => match kind {
                PointerKind::Box | PointerKind::Shr => self.build_pattern(pointee),
                PointerKind::Mut => {
                    Pat::RecP(vec![(Ident::bound("current"), self.build_pattern(pointee))])
                }
            },
        }
    }

    fn build_vc_slice(
        &self,
        t: &[(&Term<'tcx>, Ident)],
        mut q: Exp,
    ) -> Result<Exp, VCError<'tcx>>  {
        for &(field, hole) in t.into_iter().rev() {
            q = self.build_vc(field, &mut Post::new(q, hole))?;
        }
        Ok(q)
    }

    fn ty(&self, ty: Ty<'tcx>) -> Type {
        translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty)
    }

    fn get_var(&self, s: why3::Ident) -> Option<Ident> {
        todo!{} // self.renaming.borrow().get(&s)
    }

    fn open_scope(&self) {
        self.renaming.borrow_mut().open_scope();
    }

    fn close_scope(&self) {
        self.renaming.borrow_mut().close_scope();
    }

    fn fresh(&self, s: why3::Ident) -> Ident{
        todo!{} // self.renaming.borrow_mut().fresh(s)
    }
}
