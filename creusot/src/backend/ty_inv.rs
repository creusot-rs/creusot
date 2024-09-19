use super::{term::lower_pure, CloneSummary, Dependencies, TransId, Why3Generator};
use crate::{
    ctx::*,
    translation::{
        pearlite::{Pattern, Term, TermKind},
        traits,
    },
    util,
};
use indexmap::IndexSet;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArg, GenericArgs, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Symbol, DUMMY_SP};
use std::iter;

// Rewrite a type as a "head type" and a ssusbtitution, such that the head type applied to the substitution
// equals the type.
// The head type is used as a dependency node.
pub(crate) fn tyinv_head_and_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> (Ty<'tcx>, GenericArgsRef<'tcx>) {
    let def = || {
        // Return value to use if there is no structural invariant
        (
            Ty::new_param(tcx, 0, Symbol::intern(&format!("T"))),
            tcx.mk_args_from_iter(iter::once(GenericArg::from(ty))),
        )
    };

    if let Some((uinv_did, _)) = resolve_user_inv(tcx, ty, param_env)
        && util::is_ignore_structural_inv(tcx, uinv_did)
    {
        return def();
    }

    if is_tyinv_trivial(tcx, param_env, ty, true) {
        return def();
    }

    match ty.kind() {
        TyKind::Adt(adt_def, subst) => {
            (Ty::new_adt(tcx, *adt_def, GenericArgs::identity_for_item(tcx, adt_def.did())), subst)
        }
        TyKind::Closure(did, subst) => {
            (Ty::new_closure(tcx, *did, GenericArgs::identity_for_item(tcx, *did)), subst)
        }
        TyKind::Tuple(tys) => {
            let params = (0..tys.len())
                .map(|i| Ty::new_param(tcx, i as _, Symbol::intern(&format!("T{i}"))));
            let tup = Ty::new_tup_from_iter(tcx, params);
            let subst = tcx.mk_args_from_iter(tys.iter().map(GenericArg::from));
            (tup, subst)
        }
        TyKind::Alias(..) | TyKind::Param(_) => def(),
        _ => unimplemented!("{ty:?}"), // TODO
    }
}

pub(crate) fn is_tyinv_trivial<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
    param_is_trivial: bool,
) -> bool {
    if ty.is_closure() {
        return true;
    }

    // we cannot use a TypeWalker as it does not visit ADT field types
    let mut visited_adts = IndexSet::new();
    let mut stack = vec![ty];
    while let Some(ty) = stack.pop() {
        let (trait_did, subst) = user_inv_item(tcx, ty);
        let user_inv = traits::resolve_assoc_item_opt(tcx, param_env, trait_did, subst)
            .map(|(uinv_did, _)| util::is_ignore_structural_inv(tcx, uinv_did));

        // IF there is a user invariant AND it is not structural
        // OR ty is a param or alias AND we default to considering them trivial
        if user_inv == Some(false)
            || !param_is_trivial && matches!(ty.kind(), TyKind::Param(_) | TyKind::Alias(_, _))
            || matches!(ty.kind(), TyKind::Never)
        {
            return false;
        }

        match ty.kind() {
            TyKind::Ref(_, ty, _) | TyKind::Slice(ty) => stack.push(*ty),
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(def, substs) if def.is_box() => stack.push(substs.type_at(0)),
            TyKind::Adt(def, substs)
                if util::get_builtin(tcx, def.did()).is_some() || user_inv == Some(true) =>
            {
                // if the ADT has a structural user invariant, do not look into fields but only consider substs
                stack.extend(substs.types())
            }
            TyKind::Adt(def, substs) => {
                let did = def.did();
                if util::get_builtin(tcx, did).is_none() && visited_adts.insert(did) {
                    stack.extend(def.all_fields().map(|f| f.ty(tcx, substs)))
                }
            }
            _ => {}
        }
    }
    true
}

pub struct InvariantElaborator<'tcx> {
    default_trivial: bool,
    param_env: ParamEnv<'tcx>,
}

impl<'tcx> InvariantElaborator<'tcx> {
    pub(crate) fn new(param_env: ParamEnv<'tcx>, default_trivial: bool) -> Self {
        InvariantElaborator { default_trivial, param_env }
    }

    pub(crate) fn elaborate_inv(&self, ctx: &mut Why3Generator<'tcx>, ty: Ty<'tcx>) -> Term<'tcx> {
        let subject = Term::var(Symbol::intern("x"), ty);
        let trivial = is_tyinv_trivial(ctx.tcx, self.param_env, ty, self.default_trivial);
        let no_struct = matches!(ty.kind(), TyKind::Alias(..) | TyKind::Param(_));

        let rhs = if trivial {
            Term::mk_true(ctx.tcx)
        } else {
            let user_inv = resolve_user_inv(ctx.tcx, ty, self.param_env)
                .map(|(uinv_did, uinv_subst)| {
                    Term::call(ctx.tcx, uinv_did, uinv_subst, vec![subject.clone()])
                })
                .unwrap_or(Term::mk_true(ctx.tcx));
            if no_struct {
                user_inv
            } else {
                user_inv.conj(self.structural_invariant(
                    ctx,
                    subject.clone(),
                    ty,
                ))
            }
        };

        let inv_id = ctx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = ctx.mk_args(&[GenericArg::from(subject.ty)]);
        let lhs = Term::call(ctx.tcx, inv_id, subst, vec![subject]);

        let term = if no_struct && !trivial {
            Term::implies(lhs, rhs)
        } else {
            Term::eq(ctx.tcx, lhs, rhs)
        };

        Term::forall(term, ctx.tcx, (Symbol::intern("x"), ty))
    }

    fn structural_invariant(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        term: Term<'tcx>,
        ty: Ty<'tcx>,
    ) -> Term<'tcx> {
        if let Some((uinv_did, _)) = resolve_user_inv(ctx.tcx, ty, self.param_env)
            && util::is_ignore_structural_inv(ctx.tcx, uinv_did)
        {
            return Term::mk_true(ctx.tcx);
        }

        match ty.kind() {
            TyKind::Adt(adt_def, _) => {
                let adt_did = adt_def.did();
                if util::is_trusted(ctx.tcx, adt_did) {
                    Term::mk_true(ctx.tcx)
                } else {
                    self.build_inv_term_adt(ctx, term)
                }
            }
            TyKind::Tuple(tys) => {
                let ids = ('a'..).take(tys.len());

                let pattern = Pattern::Tuple(
                    ids.clone()
                        .into_iter()
                        .map(|id| Symbol::intern(&id.to_string()))
                        .map(Pattern::Binder)
                        .collect(),
                );
                Term {
                    kind: TermKind::Let {
                        pattern,
                        arg: Box::new(term),
                        body: Box::new(ids.into_iter().enumerate().fold(
                            Term::mk_true(ctx.tcx),
                            |acc, (ix, id)| {
                                acc.conj(self.mk_inv_call(
                                    ctx,
                                    Term::var(Symbol::intern(&id.to_string()), tys[ix]),
                                ))
                            },
                        )),
                    },
                    ty: ctx.types.bool,
                    span: DUMMY_SP,
                }
            }
            _ => unimplemented!("{ty:?}"), // TODO
        }
    }

    pub(crate) fn mk_inv_call(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        term: Term<'tcx>,
    ) -> Term<'tcx> {
        if is_tyinv_trivial(ctx.tcx, self.param_env, term.ty, self.default_trivial) {
            return Term::mk_true(ctx.tcx);
        }

        let inv_id = ctx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = ctx.mk_args(&[GenericArg::from(term.ty)]);
        let call_term = Term::call(ctx.tcx, inv_id, subst, vec![term]);
        call_term
    }

    fn build_inv_term_adt(&self, ctx: &mut Why3Generator<'tcx>, term: Term<'tcx>) -> Term<'tcx> {
        let TyKind::Adt(adt_def, subst) = term.ty.kind() else {
            unreachable!("asked to build ADT invariant for non-ADT type {:?}", term.ty)
        };

        use crate::pearlite::*;

        let mut arms: Vec<(_, Term<'tcx>)> = vec![];

        for var_def in adt_def.variants() {
            let tuple_var = var_def.ctor.is_some();

            let mut pats: Vec<Pattern<'tcx>> = vec![];
            let mut exp: Term<'tcx> = Term::mk_true(ctx.tcx);
            for (field_idx, field_def) in var_def.fields.iter().enumerate() {
                let field_name: Symbol = if tuple_var {
                    Symbol::intern(&format!("a_{field_idx}"))
                } else {
                    field_def.name
                };

                let field_ty = field_def.ty(ctx.tcx, subst);

                let var = Term::var(field_name, field_ty);
                let f_exp = self.mk_inv_call(ctx, var);
                exp = exp.conj(f_exp);
                pats.push(Pattern::Binder(field_name));
            }

            arms.push((
                Pattern::Constructor { variant: var_def.def_id, substs: subst, fields: pats },
                exp,
            ));
        }

        Term {
            kind: TermKind::Match { scrutinee: Box::new(term), arms },
            ty: ctx.types.bool,
            span: DUMMY_SP,
        }
    }
}

pub(crate) fn record_tyinv_deps<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> CloneSummary<'tcx> {
    let mut names = Dependencies::new(ctx.tcx, [TransId::TyInv(ty)]);

    let param_env = if let Some(adt) = ty.ty_adt_def() {
        ctx.tcx.param_env(adt.did())
    } else {
        ParamEnv::empty()
    };

    let inv_term = InvariantElaborator::new(param_env, false).elaborate_inv(ctx, ty);
    lower_pure(ctx, &mut names, &inv_term);

    let (id, subst) =
        resolve_user_inv(ctx.tcx, ty, param_env).unwrap_or(user_inv_item(ctx.tcx, ty));
    names.value(id, subst);

    let (_, summary) = names.provide_deps(ctx, GraphDepth::Shallow);
    summary
}

fn user_inv_item<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> (DefId, GenericArgsRef<'tcx>) {
    let trait_item_did = tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_user")).unwrap();
    (trait_item_did, tcx.mk_args(&[GenericArg::from(ty)]))
}

fn resolve_user_inv<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let (trait_did, subst) = user_inv_item(tcx, ty);
    traits::resolve_assoc_item_opt(tcx, param_env, trait_did, subst).or_else(|| {
        if traits::still_specializable(tcx, param_env, trait_did, subst) {
            Some((trait_did, subst))
        } else {
            None
        }
    })
}
