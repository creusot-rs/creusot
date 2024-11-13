use crate::contracts_items::get_creusot_item;
use rustc_hir::def_id::LocalDefId;
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId, symbol::Symbol};
use std::collections::HashMap;

#[derive(Debug, Default, Clone, TyDecodable, TyEncodable)]
pub struct CreusotItems {
    pub symbol_to_id: HashMap<Symbol, DefId>,
}

pub(crate) fn local_creusot_items(tcx: TyCtxt) -> CreusotItems {
    let mut items: CreusotItems = Default::default();

    for owner in tcx.hir().body_owners().map(LocalDefId::to_def_id) {
        if let Some(s) = get_creusot_item(tcx, owner) {
            items.symbol_to_id.insert(s, owner);
        }
    }

    items
}
