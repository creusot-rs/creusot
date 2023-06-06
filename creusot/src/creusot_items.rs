use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId, symbol::Symbol};
use std::collections::HashMap;

use crate::util;

use rustc_macros::{TyDecodable, TyEncodable};

#[derive(Debug, Default, Clone, TyDecodable, TyEncodable)]
pub struct CreusotItems {
    pub symbol_to_id: HashMap<Symbol, DefId>,
}

pub(crate) fn local_creusot_items(tcx: TyCtxt) -> CreusotItems {
    let mut items: CreusotItems = Default::default();

    for owner in tcx.hir().body_owners() {
        for attr in tcx.get_attrs_unchecked(owner.to_def_id()) {
            if util::is_attr(attr, "item") {
                let def_id = owner.to_def_id();

                items.symbol_to_id.insert(attr.value_str().unwrap(), def_id);
            }
        }
    }

    items
}
