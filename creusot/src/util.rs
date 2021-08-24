use crate::ctx::*;
use crate::translation::ty;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{DefIdTree, TyCtxt};
use why3::{
    declaration::Signature,
    mlcfg::{Constant, Exp, QName},
};

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

pub fn no_translate(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "no_translate"])
        .is_some()
}

pub fn should_translate(tcx: TyCtxt, mut def_id: DefId) -> bool {
    loop {
        if no_translate(tcx, def_id) {
            return false;
        }

        if tcx.is_closure(def_id) {
            def_id = tcx.parent(def_id).unwrap();
        } else {
            return true;
        }
    }
}

pub fn signature_of<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut NameMap<'tcx>,
    def_id: DefId,
) -> Signature {
    let sig = ctx.tcx.normalize_erasing_late_bound_regions(
        rustc_middle::ty::ParamEnv::reveal_all(),
        ctx.tcx.fn_sig(def_id),
    );

    let pre_contract = crate::specification::contract_of(ctx.tcx, def_id).unwrap();

    let mut contract = pre_contract.check_and_lower(ctx, names, def_id);

    if sig.output().is_never() {
        contract.ensures.push(Exp::Const(Constant::const_false()));
    }

    let names = ctx.tcx.fn_arg_names(def_id);

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

pub fn sysroot_path() -> String {
    use std::process::Command;
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain")).unwrap();
    let channel = toolchain["toolchain"]["channel"].as_str().unwrap();

    let output = Command::new("rustup")
        .arg("run")
        .arg(channel)
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap();

    print!("{}", String::from_utf8(output.stderr).ok().unwrap());

    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}
