use crate::ctx::TranslationCtx;
use crate::util::is_law;

pub fn validate_traits(ctx: &mut TranslationCtx) {
    let mut law_violations = Vec::new();

    for trait_item_id in ctx.hir_crate_items(()).trait_items() {
        let trait_item = ctx.hir().trait_item(trait_item_id);

        if is_law(ctx.tcx, trait_item.def_id.to_def_id()) && !trait_item.generics.params.is_empty()
        {
            law_violations.push((trait_item.def_id, trait_item.span))
        }
    }

    for (_, sp) in law_violations {
        ctx.error(sp, "Laws cannot have additional generic parameters");
    }
}
