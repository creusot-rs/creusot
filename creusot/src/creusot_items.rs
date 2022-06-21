use rustc_ast::ast::Attribute;
use rustc_hir::hir_id::HirId;
use rustc_middle::hir::map::Map;
use rustc_middle::hir::nested_filter::OnlyBodies; // use rustc_hir::intravisit::NestedVisitorMap;
use rustc_middle::ty::TyCtxt;
use rustc_span::{def_id::DefId, symbol::Symbol};
use std::collections::HashMap;

use crate::util;

use rustc_macros::{TyDecodable, TyEncodable};

#[derive(Debug, Default, Clone, TyDecodable, TyEncodable)]
pub struct CreusotItems {
    pub symbol_to_id: HashMap<Symbol, DefId>,
}

pub fn local_creusot_items(tcx: TyCtxt) -> CreusotItems {

    let mut items : CreusotItems = Default::default();
    // let mut visitor = CreusotItemCollector { tcx, creusot_items: Default::default() };
    // tcx.hir().walk_attributes(&mut visitor);

    for owner in tcx.hir().body_owners() {
        for attr in tcx.item_attrs(owner) {
            if util::is_attr(attr, "item") {
                let def_id = owner.to_def_id();

                items.symbol_to_id.insert(attr.value_str().unwrap(), def_id);
            }
        }
    }

    items
}
