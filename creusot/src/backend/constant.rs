use creusot_rustc::hir::def_id::DefId;
use rustc_middle::ty::{self, InternalSubsts};
use why3::declaration::{Decl, LetDecl, LetKind, Module};

use crate::{ctx::TranslationCtx, translation::constant::from_ty_const, util::module_name};

use super::{
    clone_map2::{CloneDepth, CloneVisibility, Namer},
    logic::stub_module,
    signature_of, Cloner,
};

pub(crate) fn translate_constant<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    mut names: Namer<'_, 'tcx>,
    def_id: DefId,
) -> Vec<Module> {
    let subst = InternalSubsts::identity_for_item(ctx.tcx, def_id);
    let uneval = ty::UnevaluatedConst::new(ty::WithOptConstParam::unknown(def_id), subst);
    let constant = ctx.mk_const(ty::ConstKind::Unevaluated(uneval), ctx.type_of(def_id));
    let res = from_ty_const(ctx, constant, ctx.param_env(def_id), ctx.def_span(def_id));

    let res = res.to_why(ctx, &mut names, None);
    let sig = signature_of(ctx, &mut names, def_id);
    let mut decls = names.to_clones(ctx, CloneVisibility::Body, CloneDepth::Deep);
    decls.push(Decl::Let(LetDecl {
        kind: Some(LetKind::Constant),
        sig: sig.clone(),
        rec: false,
        ghost: false,
        body: res,
    }));

    let stub = stub_module(ctx, names, def_id);

    let modl = Module { name: module_name(ctx, def_id), decls };
    vec![stub, modl]
}
