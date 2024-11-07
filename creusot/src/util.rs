use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{GenericArgs, GenericArgsRef, TyCtxt};

pub(crate) fn erased_identity_for_item(tcx: TyCtxt, did: DefId) -> GenericArgsRef {
    tcx.erase_regions(GenericArgs::identity_for_item(tcx, did))
}

pub(crate) fn parent_module(tcx: TyCtxt, mut id: DefId) -> DefId {
    while tcx.def_kind(id) != DefKind::Mod {
        id = tcx.parent(id);
    }
    id
}
