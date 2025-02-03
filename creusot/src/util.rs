use std::path::Path;

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{GenericArgs, GenericArgsRef, TyCtxt};
use rustc_span::Span;

use crate::options::SpanMode;

pub(crate) fn erased_identity_for_item(tcx: TyCtxt, did: DefId) -> GenericArgsRef {
    tcx.erase_regions(GenericArgs::identity_for_item(tcx, did))
}

pub(crate) fn parent_module(tcx: TyCtxt, mut id: DefId) -> DefId {
    while tcx.def_kind(id) != DefKind::Mod {
        id = tcx.parent(id);
    }
    id
}

pub(crate) fn path_of_span(tcx: TyCtxt, span: Span, span_mode: &SpanMode) -> Option<Box<Path>> {
    if matches!(span_mode, SpanMode::Off) || span.is_dummy() {
        return None;
    }

    let lo = tcx.sess.source_map().lookup_char_pos(span.lo());
    let rustc_span::FileName::Real(path) = &lo.file.name else { return None };
    let path = path.local_path()?;

    if let Some(rustc_base) = &tcx.sess.opts.real_rust_source_base_dir
        && path.starts_with(rustc_base)
    {
        // HACK: don't produce relative paths to standard library
        // HACK: this seems awfully specific to stdlib
        return None;
    }

    Some(path.into())
}
