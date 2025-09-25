//! Creusot-specific validations

mod ghost;
mod opacity;
mod purity;
mod terminates;
mod tokens_new;
mod traits;

pub(crate) use self::ghost::GhostValidate;
use self::{
    opacity::validate_opacity,
    purity::validate_purity,
    terminates::validate_terminates,
    traits::{validate_impls, validate_traits},
};

use rustc_hir::HirId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

use crate::{
    contracts_items::{get_builtin, is_extern_spec, is_no_translate, is_spec},
    ctx::TranslationCtx,
    validate::tokens_new::validate_tokens_new,
};

fn is_ghost_block(tcx: TyCtxt, id: HirId) -> bool {
    let attrs = tcx.hir_attrs(id);
    attrs
        .iter()
        .any(|a| a.path_matches(&[Symbol::intern("creusot"), Symbol::intern("ghost_block")]))
}

pub(crate) fn validate(ctx: &TranslationCtx) {
    for (&def_id, thir) in ctx.thir.iter() {
        let def_id = def_id.to_def_id();
        if get_builtin(ctx.tcx, def_id).is_some() || ctx.intrinsic(def_id).synthetic() {
            continue;
        }
        if is_spec(ctx.tcx, def_id) || !is_no_translate(ctx.tcx, def_id) {
            validate_purity(ctx, def_id, thir);
            validate_tokens_new(ctx, def_id, thir);
        }
        if is_extern_spec(ctx.tcx, def_id) || !is_no_translate(ctx.tcx, def_id) {
            validate_opacity(ctx, def_id);
        }
    }
    validate_terminates(ctx);
    validate_traits(ctx);
    validate_impls(ctx);
}
