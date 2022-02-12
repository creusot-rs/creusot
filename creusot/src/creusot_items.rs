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
    let mut visitor = CreusotItemCollector { tcx, creusot_items: Default::default() };

    tcx.hir().walk_attributes(&mut visitor);

    visitor.creusot_items
}

struct CreusotItemCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    creusot_items: CreusotItems,
}

impl rustc_hir::intravisit::Visitor<'tcx> for CreusotItemCollector<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Map<'tcx> {
        self.tcx.hir()
    }

    fn visit_attribute(&mut self, id: HirId, attr: &Attribute) {
        if util::is_attr(attr, "item") {
            let def_id = self.tcx.hir().local_def_id(id).to_def_id();

            self.creusot_items.symbol_to_id.insert(attr.value_str().unwrap(), def_id);
        }
    }
}
