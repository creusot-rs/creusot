use rustc_hir::def::DefKind;

use crate::{
    ctx::TranslationCtx,
    translation::specification::is_overloaded_item,
    util::{self, is_law},
};

// Validate that laws have no additional generic parameters.
//  TODO(xavier): Why was this necessary?
pub(crate) fn validate_traits(ctx: &mut TranslationCtx) {
    let mut law_violations = Vec::new();

    for trait_item_id in ctx.hir_crate_items(()).trait_items() {
        let trait_item = ctx.hir().trait_item(trait_item_id);

        if is_law(ctx.tcx, trait_item.owner_id.def_id.to_def_id())
            && !ctx.generics_of(trait_item.owner_id.def_id).params.is_empty()
        {
            law_violations.push((trait_item.owner_id.def_id, trait_item.span))
        }
    }

    for (_, sp) in law_violations {
        ctx.error(sp, "Laws cannot have additional generic parameters");
    }
}

pub(crate) fn validate_impls(ctx: &TranslationCtx) {
    for impl_id in ctx.all_local_trait_impls(()).values().flat_map(|i| i.iter()) {
        if !matches!(ctx.def_kind(*impl_id), DefKind::Impl { .. }) {
            continue;
        }

        let trait_ref = ctx.impl_trait_ref(*impl_id).unwrap().0;

        if util::is_trusted(ctx.tcx, trait_ref.def_id)
            != util::is_trusted(ctx.tcx, impl_id.to_def_id())
        {
            let msg = if util::is_trusted(ctx.tcx, trait_ref.def_id) {
                format!(
                    "Expected implementation of trait `{}` for `{}` to be marked as `#[trusted]`",
                    trait_ref.print_only_trait_name(),
                    trait_ref.self_ty()
                )
            } else {
                format!(
                    "Cannot have trusted implementation of untrusted trait `{}`",
                    trait_ref.print_only_trait_name()
                )
            };
            ctx.error(ctx.def_span(impl_id.to_def_id()), &msg)
        }

        let implementors = ctx.impl_item_implementor_ids(impl_id.to_def_id());

        let implementors =
            ctx.with_stable_hashing_context(|hcx| implementors.to_sorted(&hcx, true));
        for (trait_item, impl_item) in implementors {
            if is_overloaded_item(ctx.tcx, *trait_item) {
                continue;
            };

            if util::item_type(ctx.tcx, *trait_item) != util::item_type(ctx.tcx, *impl_item) {
                eprintln!(
                    "{:?} != {:?}",
                    util::item_type(ctx.tcx, *trait_item),
                    util::item_type(ctx.tcx, *impl_item)
                );
                ctx.error(
                    ctx.def_span(impl_item),
                    &format!(
                        "Expected `{}` to be a {} as specified by the trait declaration",
                        ctx.item_name(*impl_item),
                        util::item_type(ctx.tcx, *impl_item).to_str()
                    ),
                );
            }
        }
    }
}
