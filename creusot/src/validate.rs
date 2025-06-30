//! Creusot-specific validations

mod ghost;
mod opacity;
mod purity;
mod terminates;
mod traits;

pub(crate) use self::ghost::GhostValidate;
use self::{
    opacity::validate_opacity,
    purity::validate_purity,
    terminates::validate_terminates,
    traits::{validate_impls, validate_traits},
};

use rustc_hir::{HirId, def_id::DefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

use crate::{
    backend::is_trusted_item,
    contracts_items::{
        get_builtin, is_ghost_deref, is_ghost_deref_mut, is_logic, is_snapshot_deref, is_spec,
        is_trusted,
    },
    ctx::TranslationCtx,
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

fn is_overloaded_item(tcx: TyCtxt, def_id: DefId) -> bool {
    // These methods are allowed to cheat the purity restrictions because they are lang items we cannot redefine
    if let Some(name) = tcx.get_diagnostic_name(def_id) {
        match name.as_str() {
            "box_new" => true,
            _ => {
                is_snapshot_deref(tcx, def_id)
                    || is_ghost_deref(tcx, def_id)
                    || is_ghost_deref_mut(tcx, def_id)
            }
        }
    } else {
        false
    }
}

fn is_ghost_block(tcx: TyCtxt, id: HirId) -> bool {
    let attrs = tcx.hir().attrs(id);
    attrs
        .iter()
        .any(|a| a.path_matches(&[Symbol::intern("creusot"), Symbol::intern("ghost_block")]))
}

pub(crate) fn validate(ctx: &TranslationCtx) {
    for (&def_id, thir) in ctx.thir.iter() {
        validate_purity(ctx, def_id, thir);
        let def_id = def_id.to_def_id();
        if (is_spec(ctx.tcx, def_id) || is_logic(ctx.tcx, def_id))
            && !is_trusted_item(ctx.tcx, def_id)
        {
            validate_opacity(ctx, def_id);
        }
    }
    validate_terminates(ctx);
    validate_traits(ctx);
    validate_impls(ctx);
    validate_trusted(ctx);
}
