use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{DefIdTree, TyCtxt};
use why3::{declaration::Signature, mlcfg::{Exp, Constant, QName}};
use crate::ctx::TranslationCtx;
use crate::ty;

pub fn parent_module(tcx: TyCtxt, def_id: DefId) -> DefId {
    let mut module_id = def_id;

    while let Some(parent) = tcx.parent(module_id) {
        module_id = parent;
        if tcx.def_kind(module_id) == DefKind::Mod {
            break;
        }
    }
    module_id
}

// TODO: Unify with `Extern`
pub fn signature_of(ctx: &mut TranslationCtx<'_, '_>, def_id: DefId) -> Signature {
    let sig = ctx.tcx.normalize_erasing_late_bound_regions(
        rustc_middle::ty::ParamEnv::reveal_all(),
        ctx.tcx.fn_sig(def_id),
    );
    let names = ctx.tcx.fn_arg_names(def_id);

    let pre_contract = crate::specification::contract_of(ctx.tcx, def_id).unwrap();
    let module_id = crate::util::parent_module(ctx.tcx, def_id);

    let mut contract = pre_contract.check_and_lower(
        &crate::specification::RustcResolver(ctx.resolver.clone(), module_id, ctx.tcx),
        ctx,
        def_id,
    );

    if sig.output().is_never() {
        contract.ensures.push(Exp::Const(Constant::const_false()));
    }

    Signature {
        // TODO: consider using the function's actual name instead of impl so that trait methods and normal functions have same structure
        name: QName::from_string("impl").unwrap(),
        // TODO: use real span
        retty: Some(ty::translate_ty(ctx, rustc_span::DUMMY_SP, sig.output())),
        args: names
            .iter()
            .zip(sig.inputs())
            .map(|(id, ty)| {
                (id.name.to_string().into(), ty::translate_ty(ctx, rustc_span::DUMMY_SP, ty))
            })
            .collect(),
        contract,
    }
}