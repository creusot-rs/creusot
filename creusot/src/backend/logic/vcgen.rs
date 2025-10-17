use crate::{
    backend::{
        Why3Generator,
        clone_map::Namer as _,
        logic::Dependencies,
        program::{PtrCastKind, ptr_cast_kind},
        projections::{borrow_generated_id, projections_term},
        signature::lower_contract,
        term::{
            binop_function, binop_right_int, binop_to_binop, lower_literal, lower_pure,
            tyconst_to_term_final, unsupported_cast,
        },
        ty::{constructor, ity_to_prelude, translate_ty, uty_to_prelude},
    },
    contracts_items::{Intrinsic, is_builtin_ascription},
    ctx::{HasTyCtxt, PreMod},
    naming::name,
    translation::{
        pearlite::{
            BinOp, Literal, Pattern, PatternKind, Term, TermKind, UnOp,
            visit::{TermVisitor, super_visit_term},
        },
        traits::TraitResolved,
    },
    util::erased_identity_for_item,
};
use rustc_ast::Mutability;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::ProjectionElem,
    ty::{EarlyBinder, Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::Span;
use std::{
    collections::{HashMap, HashSet},
    iter::repeat_n,
};
use why3::{
    Exp, Ident, Name,
    exp::{Pattern as WPattern, UnOp as WUnOp},
    ty::Type,
};

/// Verification conditions for lemma functions.
///
/// As the `let functions` of Why3 leave a lot to be desired and generally cause
/// an impedence mismatch with the rest of Creusot, we have instead implemented
/// a custom VCGen for logic functions.
///
/// This VCGen is a sort of cross between WP and an evaluator, we impose a
/// certain 'evaluation order' on the logical formula so that we can validate
/// the preconditions of function calls and leverage the structure of the lemma
/// function as the proof skeleton.
///
/// There are several intersting / atypical rules here:
///
/// 1. Conjunction: 2. Exists & Forall: 3. Function calls:
///
/// TODO: Finish doc
struct VCGen<'a, 'tcx> {
    ctx: &'a Why3Generator<'tcx>,
    names: &'a Dependencies<'a, 'tcx>,
    self_id: DefId,
    structurally_recursive: bool,
    args_names: Vec<Ident>,
    variant: Option<Exp>,
    typing_env: TypingEnv<'tcx>,
}

/// Compute weakest precondition for the function `self_id`
pub(super) fn wp<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &Dependencies<'_, 'tcx>,
    self_id: DefId,
    args_names: Vec<Ident>,
    variant: Option<Exp>,
    t: Term<'tcx>,
    dest: Ident,
    post: Exp,
) -> Result<Exp, VCError<'tcx>> {
    let structurally_recursive = is_structurally_recursive(ctx, self_id, &t);
    let vcgen = VCGen {
        typing_env: ctx.typing_env(self_id),
        ctx,
        names,
        self_id,
        structurally_recursive,
        args_names,
        variant,
    };
    vcgen.build_wp(&t, &|exp| Ok(Exp::let_(dest, exp, post.clone())))
}

/// Verifies whether a given term is structurally recursive: that is, each
/// recursive call is made to a component of an argument to the prior call.
///
/// The check must also ensure that we are always recursing on the *same*
/// argument since otherwise we could 'ping pong' infinitely.
///
/// Currently, the check is *very* naive: we only consider variables and only
/// check `match`. This means that something like the following would fail:
///
/// ``` match x { Cons(_, tl) => recursive((tl, 0).0) } ```
///
/// This check can be extended in the future
fn is_structurally_recursive<'tcx>(
    ctx: &Why3Generator<'tcx>,
    self_id: DefId,
    t: &Term<'tcx>,
) -> bool {
    struct StructuralRecursion {
        smaller_than: HashMap<Ident, Ident>,
        self_id: DefId,
        /// Index of the decreasing argument
        decreasing_args: HashSet<Ident>,
        orig_args: Vec<Ident>,
    }

    impl StructuralRecursion {
        fn valid(&self) -> bool {
            self.decreasing_args.len() == 1
        }

        /// Is `t` smaller than the argument `nm`?
        fn is_smaller_than(&self, t: &Term, nm: Ident) -> bool {
            match &t.kind {
                TermKind::Var(s) => self.smaller_than.get(&s.0) == Some(&nm),
                TermKind::Coerce { arg } => self.is_smaller_than(arg, nm),
                _ => false,
            }
        }

        // TODO: could make this a `pattern` to term comparison to make it more powerful
        /// Mark `nm` as smaller than `term`. Currently, this only updates the relation if `term` is a variable.
        fn smaller_than(&mut self, nm: Ident, term: &Term<'_>) {
            match &term.kind {
                TermKind::Var(var) => {
                    let parent = self.smaller_than.get(&var.0).unwrap_or(&var.0);
                    self.smaller_than.insert(nm, *parent);
                }
                TermKind::Coerce { arg } => self.smaller_than(nm, arg),
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
                    for (name, _) in binder {
                        self.smaller_than.remove(&name.0);
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

    let orig_args = ctx.sig(self_id).inputs.iter().map(|a| a.0.0).collect();
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
    /// Inferred pre- / postconditions should not appear in these terms
    PrePostInLemma(Span),
    /// Variants are currently restricted to `Int`
    #[allow(dead_code)] // this lint is too agressive
    UnsupportedVariant(Ty<'tcx>, Span),
}

impl VCError<'_> {
    pub fn span(&self) -> Span {
        match self {
            VCError::OldInLemma(s)
            | VCError::UnsupportedVariant(_, s)
            | VCError::PrePostInLemma(s) => *s,
        }
    }
}

// We use Fn because some continuations may be called several times (in the case
// the post condition appears several times).
type PostCont<'a, 'tcx, A, R = Exp> = &'a dyn Fn(A) -> Result<R, VCError<'tcx>>;

impl<'tcx> VCGen<'_, 'tcx> {
    fn lower_literal(&self, lit: &Literal<'tcx>) -> Exp {
        lower_literal(self.ctx, self.names, lit)
    }

    fn lower_pure(&self, lit: &Term<'tcx>) -> Exp {
        lower_pure(self.ctx, self.names, lit)
    }

    fn build_wp(&self, t: &Term<'tcx>, k: PostCont<'_, 'tcx, Exp>) -> Result<Exp, VCError<'tcx>> {
        use BinOp::*;
        match &t.kind {
            // VC(v, Q) = Q(v)
            TermKind::Var(v) => k(Exp::var(v.0)),
            // VC(l, Q) = Q(l)
            TermKind::Lit(l) => k(self.lower_literal(l)),
            TermKind::SeqLiteral(elts) => self.build_wp_slice(elts, &|elts: Box<[Exp]>| {
                k(Exp::qvar(name::seq_create())
                    .app([Exp::int(elts.len() as i128), Exp::FunLiteral(elts)]))
            }),
            TermKind::Cast { arg } => match arg.ty.kind() {
                TyKind::Bool => self.build_wp(arg, &|arg| {
                    let (fct_name, prelude_kind) = match t.ty.kind() {
                        TyKind::Int(ity) => ("of_bool", ity_to_prelude(self.ctx.tcx, *ity)),
                        TyKind::Uint(uty) => ("of_bool", uty_to_prelude(self.ctx.tcx, *uty)),
                        _ if self.ctx.int_ty() == t.ty => ("to_int", PreMod::Bool),
                        _ => self.crash_and_error(
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
                            format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    // of
                    let of_fct_name = if self.names.bitwise_mode() { "of_BV256" } else { "of_int" };
                    let of_prelude = match t.ty.kind() {
                        TyKind::Int(ity) => ity_to_prelude(self.ctx.tcx, *ity),
                        TyKind::Uint(ity) => uty_to_prelude(self.ctx.tcx, *ity),
                        _ => self.ctx.crash_and_error(
                            t.span,
                            format!("casts {:?} are currently unsupported", arg.ty.kind()),
                        ),
                    };

                    self.build_wp(arg, &|arg| {
                        let to_qname = self.names.in_pre(to_prelude, to_fct_name);
                        let of_qname = self.names.in_pre(of_prelude, of_fct_name);
                        k(Exp::qvar(of_qname).app([Exp::qvar(to_qname).app([arg])]))
                    })
                }
                // Pointer-to-pointer casts
                TyKind::RawPtr(ty1, _) if let TyKind::RawPtr(ty2, _) = t.ty.kind() => {
                    match ptr_cast_kind(self.ctx.tcx, self.names.typing_env(), ty1, ty2) {
                        PtrCastKind::Id => self.build_wp(arg, k),
                        PtrCastKind::Thin => self.build_wp(arg, &|arg| {
                            let thin = self.names.in_pre(PreMod::Opaque, "thin");
                            k(Exp::qvar(thin).app([arg]))
                        }),
                        PtrCastKind::Unknown => unsupported_cast(self.ctx, t.span, arg.ty, t.ty),
                    }
                }
                _ => unsupported_cast(self.ctx, t.span, arg.ty, t.ty),
            },
            TermKind::Coerce { arg } => self.build_wp(arg, k),
            // Items are just global names so
            // VC(i, Q) = Q(i)
            TermKind::Item(id, subst) => {
                if *id == self.self_id {
                    self.ctx.crash_and_error(t.span, "cannot refer to the function in its own definition.")
                }
                // We pull (id, subst) as a dependency, because it may be useful for the proof
                let item_name = self.names.item(*id, subst);
                if let TyKind::FnDef(_, _) = self.ctx.type_of(id).instantiate_identity().kind() {
                    k(Exp::unit())
                } else {
                    k(Exp::Var(item_name))
                }
            }
            TermKind::Const(c) => {
                self.build_wp(
                    &tyconst_to_term_final(*c, t.ty, self.names.source_id(), self.ctx, self.typing_env, t.span),
                    k,
                )
            },
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
                    .normalize(self.ctx, self.typing_env);

                let variant = if self.ctx.should_check_variant_decreases(self.self_id, *id) {
                    let subst = self.ctx.normalize_erasing_regions(self.typing_env, *subst);
                    let subst_id = erased_identity_for_item(self.ctx.tcx, *id);
                    if subst != subst_id {
                        self.ctx.crash_and_error(t.span, "polymorphic recursion is not supported.")
                    }
                    if self.self_id != *id {
                        self.ctx
                            .dcx()
                            .struct_span_fatal(
                                t.span,
                                "mutual recursive calls in logic are not supported",
                            )
                            .with_note(format!(
                                "calling {} from {}",
                                self.ctx.def_path_str(*id),
                                self.ctx.def_path_str(self.self_id)
                            ))
                            .emit();
                    }

                    let variant = pre_sig.contract.variant.clone();
                    if let Some(variant) = variant {
                        self.build_variant(&args, variant)?
                    } else if self.structurally_recursive {
                        Exp::mk_true()
                    } else {
                        self.ctx.crash_and_error(
                            self.ctx.def_span(self.self_id),
                            "this function is recursive, but it does not use a variant and it not structurally recursive.",
                        )
                    }
                } else {
                    Exp::mk_true()
                };

                let mut call = Exp::Var(self.names.item(*id, subst)).app(args.clone());
                if is_builtin_ascription(self.ctx.tcx, *id) {
                    call = call.ascribe(self.ty(t.ty, t.span))
                }
                let call_subst = pre_sig
                    .inputs
                    .iter()
                    .zip(args)
                    .map(|((nm, _, _), arg)| (nm.0, arg))
                    .chain(std::iter::once((name::result(), call.clone())))
                    .collect();
                let mut contract = lower_contract(self.ctx, self.names, pre_sig.contract);
                contract.subst(&call_subst);

                let post = contract
                    .requires_conj_labelled()
                    .log_and(variant)
                    .log_and(contract.ensures_conj().implies(k(call)?));

                Ok(post)
            }),

            // VC(A && B, Q) = VC(A, |a| if a then VC(B, Q) else Q(false))
            // VC(A || B, Q) = VC(A, |a| if a then Q(true) else VC(B, Q))
            // VC(A OP B, Q) = VC(A, |a| VC(B, |b| Q(a OP B)))
            TermKind::Binary { op, lhs, rhs } => match op {
                And => self.build_wp(lhs, &|lhs| {
                    Ok(Exp::if_(lhs, self.build_wp(rhs, k)?, k(Exp::mk_false())?))
                }),
                Or => self.build_wp(lhs, &|lhs| {
                    Ok(Exp::if_(lhs, k(Exp::mk_true())?, self.build_wp(rhs, k)?))
                }),
                _ if let Some(fun) = binop_function(self.names, *op, t.ty.kind()) => {
                    let rhs_ty = rhs.ty.kind();
                    self.build_wp(lhs, &|lhs| {
                        self.build_wp(rhs, &|rhs| {
                            let rhs = if binop_right_int(*op) {
                                self.names.to_int_app(rhs_ty, rhs)
                            } else {
                                rhs
                            };
                            k(Exp::qvar(fun.clone()).app([lhs.clone(), rhs]))
                        })
                    })
                }
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
            // VC(forall<x> P(x), Q) => (forall<x> VC(P, true)) /\ Q(forall<x>P(x))
            // VC(exists<x> P(x), Q) => (forall<x> VC(P, true)) /\ Q(exists<x>P(x))
            TermKind::Quant { binder, body, .. } => {
                let body = self.build_wp(body, &|_| Ok(Exp::mk_true()))?;
                let body_wp =
                    Exp::forall(binder.iter().map(|(s, ty)| (s.0, self.ty(*ty, t.span))), body);
                Ok(body_wp.log_and(k(self.lower_pure(t))?))
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
                            .map(|(idx, fld)| {
                                (Name::local(self.names.tuple_field(args, idx.into())), fld)
                            })
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
            TermKind::Cur { term } => {
                self.build_wp(term, &|term| k(term.field(Name::Global(name::current()))))
            }
            // VC( ^ T, Q) = VC(T, |t| Q(^t))
            TermKind::Fin { term } => {
                self.build_wp(term, &|term| k(term.field(Name::Global(name::final_()))))
            }
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
                    if pattern.is_wildcard() && arg.is_unit() {
                        self.build_wp(body, k)
                    } else {
                        let body = self.build_wp(body, k)?.boxed();
                        Ok(Exp::Let { pattern, arg: arg.clone().boxed(), body })
                    }
                })
            }),
            // VC(A.f, Q) = VC(A, |a| Q(a.f))
            TermKind::Projection { lhs, idx } => {
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, lhs.ty);
                let field = match ty.kind() {
                    TyKind::Closure(did, substs) => self.names.field(*did, substs, *idx),
                    TyKind::Adt(def, subst) => self.names.field(def.did(), subst, *idx),
                    TyKind::Tuple(tys) if tys.len() == 1 => return self.build_wp(lhs, k),
                    TyKind::Tuple(tys) => self.names.tuple_field(tys, *idx),
                    k => unreachable!("Projection from {k:?}"),
                };

                self.build_wp(lhs, &|lhs| k(lhs.field(Name::local(field))))
            }
            // VC(&mut (*A).f, Q) = VC(A, |a| Q(&mut (*a).f))
            TermKind::Reborrow { inner, projections } => {
                // FIXME: this does not generate VCs for bounds of indices in ProjectionElem::Index
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, inner.ty);
                self.build_wp(inner, &|inner| {
                    self.build_wp_projections(projections, &|projs| {
                        let borrow_id = borrow_generated_id(
                            self.ctx,
                            self.names,
                            inner.clone(),
                            t.span,
                            &projs,
                            Clone::clone,
                        );

                        let inner_id = Ident::fresh_local("inner");
                        let subst = HashMap::from([(inner_id, inner.clone())]);
                        let [cur, fin] = [Term::cur, Term::fin].map(|cf| {
                            let t = projections_term(
                                self.ctx,
                                self.names.typing_env(),
                                cf(Term::var(inner_id, ty)),
                                &**projections,
                                |e| e,
                                None,
                                Clone::clone,
                                t.span,
                            );
                            let mut t = self.lower_pure(&t);
                            t.subst(&subst);
                            t
                        });

                        k(Exp::qvar(self.names.in_pre(PreMod::MutBor, "borrow_logic"))
                            .app([cur, fin, borrow_id]))
                    })
                })
            }
            // VC(|x| A(x), Q) = (forall<x>, VC(A(x), true)) /\ Q(|x| A(x))
            TermKind::Closure { bound, body } => {
                let body = self.build_wp(body, &|_| Ok(Exp::mk_true()))?;
                let wp_pre =
                    Exp::forall(bound.iter().map(|(s, ty)| (s.0, self.ty(*ty, t.span))), body);
                Ok(wp_pre.log_and(k(self.lower_pure(t))?))
            }
            TermKind::Old { .. } => Err(VCError::OldInLemma(t.span)),
            TermKind::Precondition { .. } | TermKind::Postcondition { .. } => {
                Err(VCError::PrePostInLemma(t.span))
            }
            TermKind::Capture(_) => unreachable!("Capture left in VCGen")
        }
    }

    fn build_pattern<A>(
        &self,
        pat: &Pattern<'tcx>,
        k: PostCont<'_, 'tcx, WPattern, A>,
    ) -> Result<A, VCError<'tcx>> {
        let pat = self.build_pattern_inner(pat);
        k(pat)
    }

    // FIXME: this is a duplicate with term::lower_pat
    // The only difference is the `bounds` parameter
    fn build_pattern_inner(&self, pat: &Pattern<'tcx>) -> WPattern {
        match &pat.kind {
            PatternKind::Constructor(variant, fields) => {
                let ty = self.names.normalize(pat.ty);
                let (var_did, subst) = match *ty.kind() {
                    TyKind::Adt(def, subst) => (def.variant(*variant).def_id, subst),
                    TyKind::Closure(did, subst) => (did, subst),
                    _ => unreachable!(),
                };
                let flds = fields.iter().map(|(fld, pat)| (*fld, self.build_pattern_inner(pat)));
                if self.ctx.def_kind(var_did) == DefKind::Variant {
                    let mut pats: Box<[_]> = ty.ty_adt_def().unwrap().variants()[*variant]
                        .fields
                        .indices()
                        .map(|_| WPattern::Wildcard)
                        .collect();

                    for (idx, pat) in flds {
                        pats[idx.as_usize()] = pat
                    }
                    WPattern::ConsP(Name::local(self.names.item_ident(var_did, subst)), pats)
                } else if fields.is_empty() {
                    WPattern::TupleP(Box::new([]))
                } else {
                    let flds: Box<[_]> = flds
                        .map(|(fld, p)| (Name::local(self.names.field(var_did, subst, fld)), p))
                        .collect();
                    WPattern::RecP(flds)
                }
            }
            PatternKind::Wildcard => WPattern::Wildcard,
            PatternKind::Binder(name) => WPattern::VarP(name.0),
            PatternKind::Bool(true) => WPattern::mk_true(),
            PatternKind::Bool(false) => WPattern::mk_false(),
            PatternKind::Tuple(pats) if pats.is_empty() => WPattern::TupleP(Box::new([])),
            PatternKind::Tuple(pats) if pats.len() == 1 => self.build_pattern_inner(&pats[0]),
            PatternKind::Tuple(pats) => {
                let ty = self.names.normalize(pat.ty);
                let TyKind::Tuple(tys) = ty.kind() else { unreachable!() };
                let flds: Box<[_]> = pats
                    .iter()
                    .enumerate()
                    .map(|(idx, pat)| {
                        (
                            Name::local(self.names.tuple_field(tys, idx.into())),
                            self.build_pattern_inner(pat),
                        )
                    })
                    .filter(|(_, f)| !matches!(f, WPattern::Wildcard))
                    .collect();
                if flds.is_empty() { WPattern::Wildcard } else { WPattern::RecP(flds) }
            }
            PatternKind::Deref(pointee) => {
                let ty = self.names.normalize(pat.ty);
                match ty.kind() {
                    TyKind::Adt(def, _) if def.is_box() => self.build_pattern_inner(pointee),
                    TyKind::Ref(_, _, Mutability::Not) => self.build_pattern_inner(pointee),
                    TyKind::Ref(_, _, Mutability::Mut) => WPattern::RecP(Box::new([(
                        Name::Global(name::current()),
                        self.build_pattern_inner(pointee),
                    )])),
                    _ => unreachable!(),
                }
            }
            PatternKind::Or(patterns) => {
                WPattern::OrP(patterns.iter().map(|p| self.build_pattern_inner(p)).collect())
            }
        }
    }

    fn build_wp_slice(
        &self,
        t: &[Term<'tcx>],
        k: PostCont<'_, 'tcx, Box<[Exp]>>,
    ) -> Result<Exp, VCError<'tcx>> {
        self.build_wp_slice_inner(0, t, k)
    }

    fn build_wp_slice_inner(
        &self,
        i: usize,
        t: &[Term<'tcx>],
        k: PostCont<'_, 'tcx, Box<[Exp]>>,
    ) -> Result<Exp, VCError<'tcx>> {
        if t.is_empty() {
            k(repeat_n(/* Dummy */ Exp::mk_true(), i).collect())
        } else {
            self.build_wp(&t[0], &|v| {
                self.build_wp_slice_inner(i + 1, &t[1..], &|mut args| {
                    args[i] = v.clone();
                    k(args)
                })
            })
        }
    }

    fn build_wp_projections(
        &self,
        projs: &[ProjectionElem<Term<'tcx>, Ty<'tcx>>],
        k: PostCont<'_, 'tcx, Box<[ProjectionElem<(Exp, Ty<'tcx>), Ty<'tcx>>]>>,
    ) -> Result<Exp, VCError<'tcx>> {
        self.build_wp_projections_inner(0, projs, k)
    }

    fn build_wp_projections_inner(
        &self,
        i: usize,
        projs: &[ProjectionElem<Term<'tcx>, Ty<'tcx>>],
        k: PostCont<'_, 'tcx, Box<[ProjectionElem<(Exp, Ty<'tcx>), Ty<'tcx>>]>>,
    ) -> Result<Exp, VCError<'tcx>> {
        if projs.is_empty() {
            k(repeat_n(/* Dummy */ ProjectionElem::Deref, i).collect())
        } else {
            let def = |p: ProjectionElem<(Exp, Ty<'tcx>), Ty<'tcx>>| {
                self.build_wp_projections_inner(i + 1, &projs[1..], &|mut projs| {
                    projs[i] = p.clone();
                    k(projs)
                })
            };
            match projs[0] {
                ProjectionElem::Index(ref ix) => self.build_wp(ix, &|idx| {
                    self.build_wp_projections_inner(i + 1, &projs[1..], &|mut projs| {
                        projs[i] = ProjectionElem::Index((idx.clone(), ix.ty));
                        k(projs)
                    })
                }),
                ProjectionElem::Deref => def(ProjectionElem::Deref),
                ProjectionElem::Field(field_idx, ty) => def(ProjectionElem::Field(field_idx, ty)),
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    def(ProjectionElem::ConstantIndex { offset, min_length, from_end })
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    def(ProjectionElem::Subslice { from, to, from_end })
                }
                ProjectionElem::Downcast(symbol, variant_idx) => {
                    def(ProjectionElem::Downcast(symbol, variant_idx))
                }
                ProjectionElem::OpaqueCast(ty) => def(ProjectionElem::OpaqueCast(ty)),
                ProjectionElem::Subtype(ty) => def(ProjectionElem::Subtype(ty)),
                ProjectionElem::UnwrapUnsafeBinder(ty) => {
                    def(ProjectionElem::UnwrapUnsafeBinder(ty))
                }
            }
        }
    }

    /// Translate a Rust type to Why3
    fn ty(&self, ty: Ty<'tcx>, span: Span) -> Type {
        translate_ty(self.ctx, self.names, span, ty)
    }

    /// Generates the expression to test the validity of the variant for
    /// a recursive call.
    ///
    /// Note that this only generates a variant for a simply recursive,
    /// non-polymorphic call.
    fn build_variant(
        &self,
        call_args: &[Exp],
        variant_after: Term<'tcx>,
    ) -> Result<Exp, VCError<'tcx>> {
        let wf_relation = Intrinsic::WellFoundedRelation.get(self.ctx);
        let variant_subst = self.ctx.tcx.mk_args(&[variant_after.ty.into()]);
        let (wf_relation, variant_subst) =
            TraitResolved::resolve_item(self.ctx.tcx, self.typing_env, wf_relation, variant_subst)
                .to_opt(wf_relation, variant_subst)
                .expect("The `WellFounded` trait should be implemented in this context");
        let wf_relation = Exp::Var(self.names.item(wf_relation, variant_subst));
        let subst: HashMap<Ident, Exp> =
            self.args_names.iter().cloned().zip(call_args.iter().cloned()).collect();
        let mut variant_after = self.lower_pure(&variant_after);
        variant_after.subst(&subst);
        let variant_before = self.variant.clone().unwrap();
        let variant_decreases = wf_relation.app([variant_before, variant_after]);
        Ok(variant_decreases)
    }
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for VCGen<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}
