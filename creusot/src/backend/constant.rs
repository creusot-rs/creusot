use rustc_hir::def_id::DefId;

use crate::ctx::TranslatedItem;

use super::Why3Generator;

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn translate_constant(&mut self, _: DefId) -> TranslatedItem {
        TranslatedItem::Constant {}
    }
}
