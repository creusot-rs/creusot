//! Creusot-specific validations

mod erasure;
mod ghost;
mod incorrect_attributes;
mod opacity;
mod purity;
mod terminates;
mod tokens_new;
mod traits;

pub(crate) use self::{
    erasure::{AnfBlock, a_normal_form_for_export, a_normal_form_without_specs},
    ghost::GhostValidate,
};

use self::{
    incorrect_attributes::validate_incorrect_attributes,
    opacity::validate_opacity,
    purity::validate_purity,
    terminates::validate_terminates,
    traits::{validate_impls, validate_traits},
};
use rustc_hir::HirId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_span::Symbol;

use crate::{
    contracts_items::{get_builtin, get_intrinsic, is_extern_spec, is_no_translate, is_spec},
    ctx::TranslationCtx,
    validate::{erasure::validate_erasures, tokens_new::validate_tokens_new},
};

fn is_ghost_block(tcx: TyCtxt, id: HirId) -> bool {
    let attrs = tcx.hir_attrs(id);
    attrs
        .iter()
        .any(|a| a.path_matches(&[Symbol::intern("creusot"), Symbol::intern("ghost_block")]))
}

pub(crate) fn is_ghost_or_snap(tcx: TyCtxt, ty: Ty) -> bool {
    match ty.kind() {
        TyKind::Adt(containing_type, _) => {
            let intr = get_intrinsic(tcx, containing_type.did());
            intr == Some(Symbol::intern("ghost")) || intr == Some(Symbol::intern("snapshot"))
        }
        _ => false,
    }
}

pub(crate) fn validate(ctx: &TranslationCtx) {
    for (&def_id, thir) in ctx.iter_local_thir() {
        let def_id = def_id.to_def_id();
        if get_builtin(ctx.tcx, def_id).is_some() || ctx.intrinsic(def_id).synthetic() {
            continue;
        }
        if is_spec(ctx.tcx, def_id) || !is_no_translate(ctx.tcx, def_id) {
            validate_purity(ctx, def_id, thir);
            validate_tokens_new(ctx, def_id, thir);
            validate_incorrect_attributes(ctx.tcx, def_id);
        }
        if is_extern_spec(ctx.tcx, def_id) || !is_no_translate(ctx.tcx, def_id) {
            validate_opacity(ctx, def_id);
        }
    }
    let variant_calls = validate_terminates(ctx);
    *ctx.variant_calls.borrow_mut() = variant_calls;
    validate_traits(ctx);
    validate_impls(ctx);
    validate_erasures(ctx);
}
