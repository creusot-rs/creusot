use super::{ty::translate_ty, CloneMap, CloneSummary, Why3Generator};
use crate::{
    ctx::*,
    translation::{function, traits},
    util,
};
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{subst::SubstsRef, AdtDef, GenericArg, ParamEnv, Ty, TyKind};
use rustc_span::{Symbol, DUMMY_SP};
use why3::{
    declaration::{Axiom, Decl, Module},
    exp::{Exp, Pattern},
    Ident,
};

pub(crate) fn build_inv_module<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    did: DefId,
) -> (Module, CloneSummary<'tcx>) {
    let mut names = CloneMap::new_inv(ctx.tcx, did, CloneLevel::Stub, true);

    let ty_name = util::item_name(ctx.tcx, did, Namespace::TypeNS);
    let axiom_name = Ident::from(format!("inv_{}", &*ty_name));
    let inv_axiom = build_inv_axiom(ctx, &mut names, did, axiom_name);

    let (clones, summary) = names.to_clones(ctx);

    let mut decls = function::own_generic_decls_for(ctx.tcx, did).collect::<Vec<_>>();
    decls.extend(clones);
    decls.push(Decl::Axiom(inv_axiom));

    (Module { name: util::inv_module_name(ctx.tcx, did), decls }, summary)
}

fn build_inv_axiom<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    did: DefId,
    name: Ident,
) -> Axiom {
    let ty = ctx.type_of(did).subst_identity();
    let param_env = ctx.param_env(did);
    let lhs: Exp = Exp::impure_qvar(names.ty_inv(ty)).app_to(Exp::pure_var("self".into()));
    let rhs = build_inv_exp(ctx, names, "self".into(), ty, param_env, true)
        .unwrap_or_else(|| Exp::mk_true());

    let axiom = Exp::Forall(
        vec![("self".into(), translate_ty(ctx, names, DUMMY_SP, ty))],
        Box::new(lhs.eq(rhs)),
    );
    Axiom { name, axiom }
}

fn build_inv_exp<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    ident: Ident,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
    destruct_adt: bool,
) -> Option<Exp> {
    let ty = ctx.normalize_erasing_regions(param_env, ty);

    let user_inv = if destruct_adt {
        resolve_user_inv(ctx, ty, param_env).map(|(uinv_did, uinv_subst)| {
            let inv_name = names.value(uinv_did, uinv_subst);
            Exp::impure_qvar(inv_name).app(vec![Exp::pure_var(ident.clone())])
        })
    } else {
        None
    };

    let struct_inv = build_inv_exp_struct(ctx, names, ident, ty, param_env, destruct_adt);

    match (user_inv, struct_inv) {
        (None, None) => None,
        (Some(inv), None) | (None, Some(inv)) => Some(inv),
        (Some(user_inv), Some(struct_inv)) => Some(user_inv.log_and(struct_inv)),
    }
}

fn build_inv_exp_struct<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    ident: Ident,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
    destruct_adt: bool,
) -> Option<Exp> {
    match ty.kind() {
        TyKind::Tuple(tys) => {
            let fields: Vec<Ident> =
                tys.iter().enumerate().map(|(i, _)| format!("a_{i}").into()).collect();

            let body = tys
                .iter()
                .enumerate()
                .flat_map(|(i, t)| {
                    build_inv_exp(ctx, names, fields[i].clone(), t, param_env, destruct_adt)
                })
                .reduce(|e1, e2| e1.log_and(e2))?;

            let pattern = Pattern::TupleP(fields.into_iter().map(Pattern::VarP).collect());
            Some(Exp::Let { pattern, arg: Box::new(Exp::pure_var(ident)), body: Box::new(body) })
        }
        TyKind::Adt(adt_def, adt_subst) if adt_def.is_box() => {
            build_inv_exp(ctx, names, ident, adt_subst[0].expect_ty(), param_env, destruct_adt)
        }
        TyKind::Adt(adt_def, subst) if destruct_adt => {
            build_inv_exp_adt(ctx, names, ident, param_env, *adt_def, subst)
        }
        TyKind::Adt(_, _) | TyKind::Param(_) => {
            let inv_fun = Exp::impure_qvar(names.ty_inv(ty));
            Some(inv_fun.app_to(Exp::pure_var(ident)))
        }
        _ => None, // TODO add more cases
    }
}

fn build_inv_exp_adt<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    ident: Ident,
    param_env: ParamEnv<'tcx>,
    adt_def: AdtDef,
    subst: SubstsRef<'tcx>,
) -> Option<Exp> {
    let mut branches = vec![];
    let mut trivial = true;

    for var_def in adt_def.variants().iter() {
        let tuple_var = var_def.ctor.is_some();

        let mut pats = vec![];
        let mut exp = Exp::mk_true();
        for (field_idx, field_def) in var_def.fields.iter().enumerate() {
            let field_name: Ident = if tuple_var {
                format!("a_{field_idx}").into()
            } else {
                field_def.name.as_str().into()
            };

            let field_ty = field_def.ty(ctx.tcx, subst);
            if let Some(field_inv) =
                build_inv_exp(ctx, names, field_name.clone(), field_ty, param_env, false)
            {
                pats.push(Pattern::VarP(field_name));
                exp = exp.log_and(field_inv);
                trivial = false;
            } else {
                pats.push(Pattern::Wildcard);
            }
        }

        let var_name = names.constructor(var_def.def_id, subst);
        branches.push((Pattern::ConsP(var_name, pats), exp));
    }

    (!trivial).then(|| Exp::Match(Box::new(Exp::pure_var(ident)), branches))
}

fn resolve_user_inv<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    let trait_did = ctx.get_diagnostic_item(Symbol::intern("creusot_invariant_user")).unwrap();
    let default_did =
        ctx.get_diagnostic_item(Symbol::intern("creusot_invariant_user_default")).unwrap();

    let (impl_did, subst) = traits::resolve_assoc_item_opt(
        ctx.tcx,
        param_env,
        trait_did,
        ctx.mk_substs(&[GenericArg::from(ty)]),
    )?;
    let subst = ctx.try_normalize_erasing_regions(param_env, subst).unwrap_or(subst);

    // if inv resolved to the default impl and is not specializable, ignore
    if impl_did == default_did && !traits::still_specializable(ctx.tcx, param_env, impl_did, subst)
    {
        None
    } else {
        Some((impl_did, subst))
    }
}
