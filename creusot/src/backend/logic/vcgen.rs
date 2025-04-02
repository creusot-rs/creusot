use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    iter::repeat_n,
};

use crate::{
    backend::{
        Namer as _, Why3Generator,
        logic::Dependencies,
        signature::lower_sig,
        term::{binop_to_binop, lower_literal, lower_pure},
        ty::{constructor, is_int, ity_to_prelude, translate_ty, uty_to_prelude},
    },
    contracts_items::get_builtin,
    ctx::PreMod,
    naming::ident_of,
    pearlite::{Literal, Pattern, PatternKind, Term, TermVisitor, super_visit_term},
    util::erased_identity_for_item,
};
use rustc_ast::Mutability;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{EarlyBinder, Ty, TyKind, TypingEnv};
use rustc_span::{Span, Symbol};
use why3::{
    Exp, Ident,
    exp::{BinOp, Environment, Pattern as WPattern, UnOp as WUnOp},
    ty::Type,
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
    ctx: &'a Why3Generator<'tcx>,
    names: &'a Dependencies<'tcx>,
    self_id: DefId,
    structurally_recursive: bool,
    args_names: Vec<Ident>,
    variant: Option<Exp>,
    typing_env: TypingEnv<'tcx>,
    subst: RefCell<Environment>,
}

pub(super) fn wp<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    self_id: DefId,
    args_names: Vec<Ident>,
    variant: Option<Exp>,
    t: Term<'tcx>,
    dest: Ident,
    post: Exp,
) -> Result<Exp, VCError<'tcx>> {
    let structurally_recursive = is_structurally_recursive(ctx, self_id, &t);
    let bounds = args_names.iter().map(|arg| (arg.clone(), Exp::var(arg.clone()))).collect();
    let vcgen = VCGen {
        typing_env: ctx.typing_env(self_id),
        ctx,
        names,
        self_id,
        structurally_recursive,
        subst: Default::default(),
        args_names,
        variant,
    };
    vcgen.add_bounds(bounds);
    vcgen.build_wp(&t, &|exp| Ok(Exp::let_(dest.clone(), exp, post.clone())))
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
                TermKind::Coerce { arg } => self.is_smaller_than(arg, nm),
                _ => false,
            }
        }

        // TODO: could make this a `pattern` to term comparison to make it more powerful
        /// Mark `sym` as smaller than `term`. Currently, this only updates the relation if `term` is a variable.
        fn smaller_than(&mut self, sym: Symbol, term: &Term<'_>) {
            match &term.kind {
                TermKind::Var(var) => {
                    let parent = self.smaller_than.get(var).unwrap_or(var);
                    self.smaller_than.insert(sym, *parent);
                }
                TermKind::Coerce { arg } => self.smaller_than(sym, arg),
                _ => (),
            }
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

// We use Fn because some continuations may be called several times (in the case
// the post condition appears several times).
type PostCont<'a, 'tcx, A, R = Exp> = &'a dyn Fn(A) -> Result<R, VCError<'tcx>>;

impl<'a, 'tcx> VCGen<'a, 'tcx> {
    fn lower_literal(&self, lit: &Literal<'tcx>) -> Exp {
        lower_literal(self.ctx, self.names, lit)
    }

    fn lower_pure(&self, lit: &Term<'tcx>) -> Exp {
        lower_pure(self.ctx, self.names, lit)
    }

    fn build_wp(&self, t: &Term<'tcx>, k: PostCont<'_, 'tcx, Exp>) -> Result<Exp, VCError<'tcx>> {
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
            TermKind::Cast { arg } => match arg.ty.kind() {
                TyKind::Bool => self.build_wp(arg, &|arg| {
                    let (fct_name, prelude_kind) = match t.ty.kind() {
                        TyKind::Int(ity) => ("of_bool", ity_to_prelude(self.ctx.tcx, *ity)),
                        TyKind::Uint(uty) => ("of_bool", uty_to_prelude(self.ctx.tcx, *uty)),
                        _ if is_int(self.ctx.tcx, t.ty) => ("to_int", PreMod::Bool),
                        _ => self.ctx.crash_and_error(
                            t.span,
                            "bool cast to non integral casts are currently unsupported",
                        ),
                    };
                    k(Exp::qvar(self.names.in_pre(prelude_kind, fct_name)).app([arg]))
                }),
                TyKind::Int(_) | TyKind::Uint(_) => {
                    // to
                    let to_fct_name = if self.names.bitwise_mode() {
                        "to_BV256"
                    } else if let TyKind::Uint(_) = arg.ty.kind() {
                        "t'int"
                    } else {
                        "to_int"
                    };
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

                    self.build_wp(arg, &|arg| {
                        let to_qname = self.names.in_pre(to_prelude, to_fct_name);
                        let of_qname = self.names.in_pre(of_prelude, of_fct_name);
                        k(Exp::qvar(of_qname).app([Exp::qvar(to_qname).app([arg])]))
                    })
                }
                _ => self.ctx.crash_and_error(t.span, "unsupported cast"),
            },
            TermKind::Coerce { arg } => self.build_wp(arg, k),
            // Items are just global names so
            // VC(i, Q) = Q(i)
            TermKind::Item(id, sub) => {
                let item_name = self.names.item(*id, sub);

                if get_builtin(self.ctx.tcx, *id).is_some() {
                    // Builtins can leverage Why3 polymorphism and sometimes can cause typeck errors in why3 due to ambiguous type variables so lets fix the type now.
                    k(Exp::qvar(item_name).ascribe(self.ty(t.ty)))
                } else {
                    k(Exp::qvar(item_name))
                }
            }
            // VC(assert { C }, Q) => VC(C, |c| c && Q(()))
            TermKind::Assert { cond } => {
                self.build_wp(cond, &|exp| Ok(exp.lazy_and(k(Exp::unit())?)))
            }
            // VC(f As, Q) = VC(A0, |a0| ... VC(An, |an|
            //  pre(f)(a0..an) /\ variant(f)(a0..an) /\ (post(f)(a0..an, F(a0..an)) -> Q(F a0..an))
            // ))
            TermKind::Call { id, subst, args } => self.build_wp_slice(args, &|args| {
                let pre_sig = EarlyBinder::bind(self.ctx.sig(*id).clone())
                    .instantiate(self.ctx.tcx, subst)
                    .normalize(self.ctx.tcx, self.typing_env);

                let arg_subst = pre_sig
                    .inputs
                    .iter()
                    .zip(&args)
                    .map(|(nm, res)| (ident_of(nm.0), res.clone()))
                    .collect();
                let variant = pre_sig.contract.variant.clone();
                let mut sig = lower_sig(self.ctx, self.names, "".into(), pre_sig, *id);

                let variant = if *id == self.self_id {
                    let subst = self.ctx.normalize_erasing_regions(self.typing_env, *subst);
                    let subst_id = erased_identity_for_item(self.ctx.tcx, *id);
                    if subst != subst_id {
                        self.ctx.crash_and_error(t.span, "Polymorphic recursion is not supported.")
                    }

                    if let Some(variant) = variant {
                        self.build_variant(&args, variant.ty, variant.span)?
                    } else {
                        if self.structurally_recursive { Exp::mk_true() } else { Exp::mk_false() }
                    }
                } else {
                    Exp::mk_true()
                };

                sig.contract.subst(&arg_subst);

                let fun = Exp::qvar(self.names.item(*id, subst));
                let call = fun.app(args);
                sig.contract.subst(&[("result".into(), call.clone())].into_iter().collect());

                let post = sig
                    .contract
                    .requires_conj_labelled()
                    .log_and(variant)
                    .log_and(sig.contract.ensures_conj().implies(k(call)?));

                Ok(post)
            }),

            // VC(A && B, Q) = VC(A, |a| if a then VC(B, Q) else Q(false))
            // VC(A || B, Q) = VC(A, |a| if a then Q(true) else VC(B, Q))
            // VC(A OP B, Q) = VC(A, |a| VC(B, |b| Q(a OP B)))
            TermKind::Binary { op, lhs, rhs } => match op {
                BinOp::And => self.build_wp(lhs, &|lhs| {
                    Ok(Exp::if_(lhs, self.build_wp(rhs, k)?, k(Exp::mk_false())?))
                }),
                BinOp::Or => self.build_wp(lhs, &|lhs| {
                    Ok(Exp::if_(lhs, k(Exp::mk_true())?, self.build_wp(rhs, k)?))
                }),
                BinOp::Div => self.build_wp(lhs, &|lhs| {
                    self.build_wp(rhs, &|rhs| k(Exp::var("div").app([lhs.clone(), rhs])))
                }),
                BinOp::Rem => self.build_wp(lhs, &|lhs| {
                    self.build_wp(rhs, &|rhs| k(Exp::var("mod").app([lhs.clone(), rhs])))
                }),
                _ => self.build_wp(lhs, &|lhs| {
                    self.build_wp(rhs, &|rhs| {
                        k(Exp::BinaryOp(binop_to_binop(*op), lhs.clone().boxed(), rhs.boxed()))
                    })
                }),
            },
            // VC(OP A, Q) = VC(A |a| Q(OP a))
            TermKind::Unary { op, arg } => self.build_wp(arg, &|arg| {
                let op = match op {
                    UnOp::Not => WUnOp::Not,
                    UnOp::Neg => WUnOp::Neg,
                };

                k(Exp::UnaryOp(op, arg.boxed()))
            }),
            // // the dual rule should be the one below but that seems weird...
            // // VC(forall<x> P(x), Q) => (exists<x> VC(P, false)) \/ Q(forall<x>P(x))
            // // Instead, I think the rule should just be the same as for the existential quantifiers?
            TermKind::Quant { kind: QuantKind::Forall, binder, body, .. } => {
                let forall_pre = self.build_wp(body, &|_| Ok(Exp::mk_true()))?;

                let forall_pre = Exp::forall(
                    zip_binder(binder).map(|(s, t)| (s.to_string().into(), self.ty(t))),
                    forall_pre,
                );
                let forall_pure = self.lower_pure(t);
                Ok(forall_pre.log_and(k(forall_pure)?))
            }
            // // VC(exists<x> P(x), Q) => (forall<x> VC(P, true)) /\ Q(exists<x>P(x))
            TermKind::Quant { kind: QuantKind::Exists, binder, body, .. } => {
                let exists_pre = self.build_wp(body, &|_| Ok(Exp::mk_true()))?;

                let exists_pre = Exp::forall(
                    zip_binder(binder).map(|(s, t)| (s.to_string().into(), self.ty(t))),
                    exists_pre,
                );
                let exists_pure = self.lower_pure(t);
                Ok(exists_pre.log_and(k(exists_pure)?))
            }
            // VC((T...), Q) = VC(T[0], |t0| ... VC(T[N], |tn| Q(t0..tn))))
            TermKind::Tuple { fields } => {
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, t.ty);
                let TyKind::Tuple(args) = ty.kind() else { unreachable!() };
                self.build_wp_slice(fields, &|flds| match flds.len() {
                    0 => k(Exp::unit()),
                    1 => k(flds.into_iter().next().unwrap()),
                    _ => k(Exp::Record {
                        fields: flds
                            .into_iter()
                            .enumerate()
                            .map(|(idx, fld)| (self.names.tuple_field(args, idx.into()), fld))
                            .collect(),
                    }),
                })
            }
            // Same as for tuples
            TermKind::Constructor { variant, fields, .. } => {
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, t.ty);
                let TyKind::Adt(adt, subst) = ty.kind() else { unreachable!() };
                self.build_wp_slice(fields, &|fields| {
                    let ctor = constructor(self.names, fields, adt.variant(*variant).def_id, subst);
                    k(ctor)
                })
            }
            // VC( * T, Q) = VC(T, |t| Q(*t))
            TermKind::Cur { term } => self.build_wp(term, &|term| k(term.field("current".into()))),
            // VC( ^ T, Q) = VC(T, |t| Q(^t))
            TermKind::Fin { term } => self.build_wp(term, &|term| k(term.field("final".into()))),
            // VC(A -> B, Q) = VC(A, VC(B, Q(A -> B)))
            TermKind::Impl { lhs, rhs } => self.build_wp(lhs, &|lhs| {
                Ok(Exp::if_(lhs, self.build_wp(rhs, k)?, k(Exp::mk_true())?))
            }),
            // VC(match A {P -> E}, Q) = VC(A, |a| match a {P -> VC(E, Q)})
            TermKind::Match { scrutinee, arms }
                if scrutinee.ty.is_bool()
                    && arms.len() == 2
                    && arms.iter().all(|a| a.0.get_bool().is_some()) =>
            {
                self.build_wp(scrutinee, &|scrut| {
                    let mut arms: Vec<_> = arms
                        .iter()
                        .map(|arm| Ok((arm.0.get_bool().unwrap(), self.build_wp(&arm.1, k)?)))
                        .collect::<Result<_, _>>()?;
                    arms.sort_by(|a, b| b.0.cmp(&a.0));

                    Ok(Exp::if_(scrut, arms.remove(0).1, arms.remove(0).1))
                })
            }

            // VC(match A {P -> E}, Q) = VC(A, |a| match a {P -> VC(E, Q)})
            TermKind::Match { scrutinee, arms } => self.build_wp(scrutinee, &|scrut| {
                let arms = arms
                    .iter()
                    .map(|arm| {
                        self.build_pattern(&arm.0, &|pat| Ok((pat, self.build_wp(&arm.1, k)?)))
                    })
                    .collect::<Result<Box<[_]>, _>>()?;

                Ok(scrut.match_(arms))
            }),
            // VC(let P = A in B, Q) = VC(A, |a| let P = a in VC(B, Q))
            TermKind::Let { pattern, arg, body } => self.build_wp(arg, &|arg| {
                self.build_pattern(pattern, &|pattern| {
                    let body = self.build_wp(body, k)?.boxed();
                    Ok(Exp::Let { pattern, arg: arg.clone().boxed(), body })
                })
            }),
            // VC(A.f, Q) = VC(A, |a| Q(a.f))
            TermKind::Projection { lhs, idx } => {
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, lhs.ty);
                let field = match ty.kind() {
                    TyKind::Closure(did, substs) => self.names.field(*did, substs, *idx),
                    TyKind::Adt(def, substs) => self.names.field(def.did(), substs, *idx),
                    TyKind::Tuple(tys) if tys.len() == 1 => return self.build_wp(lhs, k),
                    TyKind::Tuple(tys) => self.names.tuple_field(tys, *idx),
                    k => unreachable!("Projection from {k:?}"),
                };

                self.build_wp(lhs, &|lhs| k(lhs.field(field.clone())))
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
        k: PostCont<'_, 'tcx, WPattern, A>,
    ) -> Result<A, VCError<'tcx>> {
        let mut bounds = Default::default();
        let pat = self.build_pattern_inner(&mut bounds, pat);
        self.add_bounds(bounds);
        // FIXME: this totally breaks the tail-call potential... which needs desparate fixing.
        let r = k(pat);
        self.pop_bounds();
        r
    }

    // FIXME: this is a duplicate with term::lower_pat
    // The only difference is the `bounds` parameter
    fn build_pattern_inner(
        &self,
        bounds: &mut HashMap<Ident, Exp>,
        pat: &Pattern<'tcx>,
    ) -> WPattern {
        match &pat.kind {
            PatternKind::Constructor(variant, fields) => {
                let ty = self.names.normalize(self.ctx, pat.ty);
                let (var_did, subst) = match ty.kind() {
                    &TyKind::Adt(def, subst) => (def.variant(*variant).def_id, subst),
                    &TyKind::Closure(did, subst) => (did, subst),
                    _ => unreachable!(),
                };
                let flds = fields.iter().map(|pat| self.build_pattern_inner(bounds, pat));
                if self.ctx.def_kind(var_did) == DefKind::Variant {
                    WPattern::ConsP(self.names.constructor(var_did, subst), flds.collect())
                } else if fields.is_empty() {
                    WPattern::TupleP(Box::new([]))
                } else {
                    let flds: Box<[_]> = flds
                        .enumerate()
                        .map(|(i, f)| (self.names.field(var_did, subst, i.into()), f))
                        .filter(|(_, f)| !matches!(f, WPattern::Wildcard))
                        .collect();
                    if flds.len() == 0 { WPattern::Wildcard } else { WPattern::RecP(flds) }
                }
            }
            PatternKind::Wildcard => WPattern::Wildcard,
            PatternKind::Binder(name) => {
                let name_id = name.as_str().into();
                let new = self.uniq_occ(&name_id);
                bounds.insert(name_id, Exp::var(new.clone()));
                WPattern::VarP(new)
            }
            PatternKind::Bool(true) => WPattern::mk_true(),
            PatternKind::Bool(false) => WPattern::mk_false(),
            PatternKind::Tuple(pats) if pats.is_empty() => WPattern::TupleP(Box::new([])),
            PatternKind::Tuple(pats) if pats.len() == 1 => {
                self.build_pattern_inner(bounds, &pats[0])
            }
            PatternKind::Tuple(pats) => {
                let ty = self.names.normalize(self.ctx, pat.ty);
                let TyKind::Tuple(tys) = ty.kind() else { unreachable!() };
                let flds: Box<[_]> = pats
                    .iter()
                    .enumerate()
                    .map(|(idx, pat)| {
                        (
                            self.names.tuple_field(tys, idx.into()),
                            self.build_pattern_inner(bounds, pat),
                        )
                    })
                    .filter(|(_, f)| !matches!(f, WPattern::Wildcard))
                    .collect();
                if flds.len() == 0 { WPattern::Wildcard } else { WPattern::RecP(flds) }
            }
            PatternKind::Deref(pointee) => {
                let ty = self.names.normalize(self.ctx, pat.ty);
                match ty.kind() {
                    TyKind::Adt(def, _) if def.is_box() => {
                        self.build_pattern_inner(bounds, pointee)
                    }
                    TyKind::Ref(_, _, Mutability::Not) => self.build_pattern_inner(bounds, pointee),
                    TyKind::Ref(_, _, Mutability::Mut) => WPattern::RecP(Box::new([(
                        "current".into(),
                        self.build_pattern_inner(bounds, pointee),
                    )])),
                    _ => unreachable!(),
                }
            }
        }
    }

    fn uniq_occ(&self, id: &Ident) -> Ident {
        let occ = self.subst.borrow().nb_occurences(id);
        if occ == 0 { id.clone() } else { Ident::from_string(format!("{}_{occ}", &**id)) }
    }

    fn build_wp_slice(
        &self,
        t: &[Term<'tcx>],
        k: PostCont<'_, 'tcx, Box<[Exp]>>,
    ) -> Result<Exp, VCError<'tcx>> {
        self.build_wp_slice_inner(t.len(), t, k)
    }

    fn build_wp_slice_inner(
        &self,
        len: usize,
        t: &[Term<'tcx>],
        k: PostCont<'_, 'tcx, Box<[Exp]>>,
    ) -> Result<Exp, VCError<'tcx>> {
        if t.is_empty() {
            k(repeat_n(/* Dummy */ Exp::mk_true(), len).collect())
        } else {
            self.build_wp(&t[0], &|v| {
                self.build_wp_slice_inner(len, &t[1..], &|mut args| {
                    args[len - t.len()] = v.clone();
                    k(args)
                })
            })
        }
    }

    fn ty(&self, ty: Ty<'tcx>) -> Type {
        translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty)
    }

    // Generates the expression to test the validity of the variant for a recursive call.
    // Currently restricted to `Int` until we sort out `WellFounded` (soon?)
    //
    // If V is the variant expression at entry and V' is the variant expression of the recursive call it generates
    //  0 <= V && V' < V
    //  Weirdly this doesn't check `0 <= V'` but this is actually the same behavior as Why3
    fn build_variant(
        &self,
        call_args: &[Exp],
        variant_ty: Ty<'tcx>,
        span: Span,
    ) -> Result<Exp, VCError<'tcx>> {
        let mut subst: Environment =
            self.args_names.iter().cloned().zip(call_args.iter().cloned()).collect();
        let orig_variant = self.variant.clone().unwrap();
        let mut rec_var_exp = orig_variant.clone();
        rec_var_exp.subst(&mut subst);
        if is_int(self.ctx.tcx, variant_ty) {
            self.names.import_prelude_module(PreMod::Int);
            let orig_variant = orig_variant.boxed();
            Ok(Exp::BinaryOp(BinOp::Le, Exp::int(0).boxed(), orig_variant.clone())
                .log_and(Exp::BinaryOp(BinOp::Lt, rec_var_exp.boxed(), orig_variant)))
        } else {
            Err(VCError::UnsupportedVariant(variant_ty, span))
        }
    }

    fn add_bounds(&self, bounds: HashMap<Ident, Exp>) {
        self.subst.borrow_mut().add_subst(bounds);
    }

    fn pop_bounds(&self) {
        self.subst.borrow_mut().pop_subst();
    }
}
