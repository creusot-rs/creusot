use crate::ctx::TranslationCtx;
use crate::util::is_law;
use rustc_hir::def_id::LocalDefId;
// use rustc_hir::itemlikevisit::ItemLikeVisitor;
use rustc_hir::{ForeignItem, ImplItem, Item, TraitItem};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

struct LawParams<'tcx> {
    tcx: TyCtxt<'tcx>,
    law_violations: Vec<(LocalDefId, Span)>,
}

// impl<'hir, 'tcx> ItemLikeVisitor<'hir> for LawParams<'tcx> {
//     fn visit_item(&mut self, _: &'hir Item<'hir>) {}
//     fn visit_trait_item(&mut self, trait_item: &'hir TraitItem<'hir>) {
//         if is_law(self.tcx, trait_item.def_id.to_def_id()) && !trait_item.generics.params.is_empty()
//         {
//             self.law_violations.push((trait_item.def_id, trait_item.span))
//         }
//     }
//     fn visit_impl_item(&mut self, _: &'hir ImplItem<'hir>) {}
//     fn visit_foreign_item(&mut self, _: &'hir ForeignItem<'hir>) {}
// }

pub fn validate_traits(ctx: &mut TranslationCtx) {
    // let mut law_visitor = LawParams { tcx: ctx.tcx, law_violations: Vec::new() };

    // ctx.tcx.hir().visit_all_item_likes(&mut law_visitor);

    // for (_, sp) in law_visitor.law_violations {
    //     ctx.error(sp, "Laws cannot have additional generic parameters");
    // }
}
