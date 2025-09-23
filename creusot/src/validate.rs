//! Creusot-specific validations

mod erasure;
mod ghost;
mod opacity;
mod purity;
mod terminates;
mod tokens_new;
mod traits;

pub(crate) use self::{
    erasure::{AnfBlock, a_normal_form, a_normal_form_without_specs},
    ghost::{GhostValidate, is_ghost_ty_},
};

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
    contracts_items::{get_builtin, is_extern_spec, is_no_translate, is_spec, is_trusted},
    ctx::{HasTyCtxt as _, TranslationCtx},
    validate::{erasure::validate_erasures, tokens_new::validate_tokens_new},
};

/// Validate that creusot buitins are annotated with `#[trusted]`.
fn validate_trusted(ctx: &TranslationCtx) {
    for def_id in ctx.hir_crate_items(()).definitions() {
        let def_id = def_id.to_def_id();
        if get_builtin(ctx.tcx, def_id).is_some() && !is_trusted(ctx.tcx, def_id) {
            ctx.error(
                ctx.def_span(def_id),
                "Builtin declarations should be annotated with #[trusted].",
            )
            .emit();
        }
    }
}

fn is_ghost_block(tcx: TyCtxt, id: HirId) -> bool {
    let attrs = tcx.hir_attrs(id);
    attrs
        .iter()
        .any(|a| a.path_matches(&[Symbol::intern("creusot"), Symbol::intern("ghost_block")]))
}

pub(crate) fn validate(ctx: &TranslationCtx) {
    for (&def_id, thir) in ctx.iter_local_thir() {
        let def_id = def_id.to_def_id();
        if is_spec(ctx.tcx, def_id) || !is_no_translate(ctx.tcx, def_id) {
            validate_purity(ctx, def_id, thir);
            validate_tokens_new(ctx, def_id, thir);
        }
        if is_extern_spec(ctx.tcx, def_id) || !is_no_translate(ctx.tcx, def_id) {
            validate_opacity(ctx, def_id);
        }
    }
    let variant_calls = validate_terminates(ctx);
    *ctx.variant_calls.borrow_mut() = variant_calls;
    validate_traits(ctx);
    validate_impls(ctx);
    validate_trusted(ctx);
    validate_erasures(ctx);
}
