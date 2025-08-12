use rustc_hir::def::DefKind;

use crate::{
    contracts_items::{
        is_law, is_open_inv_result, is_snapshot_deref, is_snapshot_deref_mut, is_trusted,
    },
    ctx::{HasTyCtxt as _, TranslationCtx},
};

/// Validate that laws have no additional generic parameters.
///
/// This is because laws are auto-loaded, and we do not want to generate polymorphic WhyML code.
pub(crate) fn validate_traits(ctx: &TranslationCtx) {
    let mut law_violations = Vec::new();

    for trait_item_id in ctx.hir_crate_items(()).trait_items() {
        let trait_item = ctx.hir().trait_item(trait_item_id);

        if is_law(ctx.tcx, trait_item.owner_id.def_id.to_def_id())
            && !(ctx.predicates_of(trait_item.owner_id.def_id).predicates.is_empty()
                && ctx.generics_of(trait_item.owner_id.def_id).own_params.is_empty())
        {
            law_violations.push((trait_item.owner_id.def_id, trait_item.span))
        }
    }

    for (_, sp) in law_violations {
        ctx.error(sp, "Laws cannot have additional generic parameters or trait constraints").emit();
    }
}

/// Validates that trait implementations have some of the same attributes as the trait item.
///
/// # Example
///
/// ```creusot
/// trait Tr {
///     #[logic]
///     fn foo();
///     #[check(terminates)]
///     fn bar();
/// }
///
/// impl Tr for MyType {
///     fn foo() {} // ! ERROR ! foo should be marked `#[logic]`
///     fn bar() {} // ! ERROR ! bar should be marked `#[check(terminates)]`
/// }
/// ```
pub(crate) fn validate_impls(ctx: &TranslationCtx) {
    for impl_id in ctx.all_local_trait_impls(()).values().flat_map(|i| i.iter()) {
        if !matches!(ctx.def_kind(*impl_id), DefKind::Impl { .. }) {
            continue;
        }
        use rustc_middle::ty::print::PrintTraitRefExt;
        let trait_ref = ctx.impl_trait_ref(*impl_id).unwrap().skip_binder();

        if is_trusted(ctx.tcx, trait_ref.def_id) != is_trusted(ctx.tcx, impl_id.to_def_id()) {
            let msg = if is_trusted(ctx.tcx, trait_ref.def_id) {
                format!(
                    "Expected implementation of trait `{}` for `{}` to be marked as `#[trusted]`",
                    trait_ref.print_only_trait_path(),
                    trait_ref.self_ty()
                )
            } else {
                format!(
                    "Cannot have trusted implementation of untrusted trait `{}`",
                    trait_ref.print_only_trait_path()
                )
            };
            ctx.error(ctx.def_span(impl_id.to_def_id()), msg).emit();
        }

        let implementors = ctx.impl_item_implementor_ids(impl_id.to_def_id());

        let implementors =
            ctx.with_stable_hashing_context(|hcx| implementors.to_sorted(&hcx, true));
        for (&trait_item, &impl_item) in implementors {
            if !ctx.def_kind(trait_item).is_fn_like() {
                continue;
            }

            if let Some(open_inv_trait) = ctx.params_open_inv(trait_item) {
                let open_inv_impl = ctx.params_open_inv(impl_item).unwrap();
                for &i in open_inv_trait {
                    if !open_inv_impl.contains(&i) {
                        let name_param = ctx.fn_arg_names(impl_item)[i];
                        ctx.error(
                            ctx.def_span(impl_item),
                            format!(
                                "Parameter `{name_param}` has the `#[creusot::open_inv]` attribute in the trait declaration, but not in the implementation."
                            ),
                        ).emit();
                    }
                }
            }

            if is_open_inv_result(ctx.tcx, impl_item) && !is_open_inv_result(ctx.tcx, trait_item) {
                ctx.error(
                    ctx.def_span(impl_item),
                    format!(
                        "Function `{}` should not have the `#[open_inv_result]` attribute, as specified by the trait declaration",
                        ctx.item_name(impl_item),
                    ),
                ).emit();
            }

            if is_snapshot_deref(ctx.tcx, impl_item) || is_snapshot_deref_mut(ctx.tcx, impl_item) {
                continue;
            };

            let item_type = ctx.item_type(impl_item);
            let trait_type = ctx.item_type(trait_item);
            if !item_type.can_implement(trait_type) {
                ctx.error(
                    ctx.def_span(impl_item),
                    format!(
                        "Expected `{}` to be a {} as specified by the trait declaration",
                        ctx.item_name(impl_item),
                        trait_type.to_str()
                    ),
                )
                .emit();
            } else {
                let item_contract = &ctx.sig(impl_item).contract;
                let trait_contract = &ctx.sig(trait_item).contract;
                if trait_contract.no_panic && !item_contract.no_panic {
                    ctx.error(
                        ctx.def_span(impl_item),
                        format!(
                            "Expected `{}` to be `#[check(ghost)]` as specified by the trait declaration",
                            ctx.item_name(impl_item),
                        ),
                    )
                    .emit();
                } else if trait_contract.terminates && !item_contract.terminates {
                    ctx.error(
                        ctx.def_span(impl_item),
                        format!(
                            "Expected `{}` to be `#[check(terminates)]` as specified by the trait declaration",
                            ctx.item_name(impl_item),
                        ),
                    )
                    .emit();
                } else if is_law(ctx.tcx, impl_item) && !is_law(ctx.tcx, trait_item) {
                    ctx.error(
                        ctx.def_span(impl_item),
                        format!(
                            "Method `{}` should not be a `#[law]`, as specified by the trait declaration",
                            ctx.item_name(impl_item),
                        ),
                    )
                    .emit();
                } else if !is_law(ctx.tcx, impl_item) && is_law(ctx.tcx, trait_item) {
                    ctx.error(
                        ctx.def_span(impl_item),
                        format!(
                            "Expected `{}` to be a `#[law]` as specified by the trait declaration",
                            ctx.item_name(impl_item),
                        ),
                    )
                    .emit();
                }
            }
        }
    }
}
