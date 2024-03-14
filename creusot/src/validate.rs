use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::Visibility;
use rustc_span::Span;

use crate::{
    ctx::{parent_module, TranslationCtx},
    translation::{
        pearlite::{super_visit_term, TermKind, TermVisitor},
        specification::is_overloaded_item,
    },
    util::{self, is_law},
};

pub(crate) fn validate_opacity(ctx: &mut TranslationCtx, item: DefId) -> Option<()> {
    struct OpacityVisitor<'a, 'tcx> {
        ctx: &'a TranslationCtx<'tcx>,
        opacity: Option<DefId>,
        source_item: DefId,
    }

    impl<'a, 'tcx> OpacityVisitor<'a, 'tcx> {
        fn is_visible_enough(&self, id: DefId) -> bool {
            match self.opacity {
                None => self.ctx.visibility(id) == Visibility::Public,
                Some(opa) => self.ctx.visibility(id).is_accessible_from(opa, self.ctx.tcx),
            }
        }

        fn error(&self, id: DefId, span: Span) -> () {
            self.ctx.error(
                span,
                &format!(
                    "Cannot make `{:?}` transparent in `{:?}` as it would call a less-visible item.",
                    self.ctx.def_path_str(id), self.ctx.def_path_str(self.source_item)
                ),
            ).emit();
        }
    }

    impl<'a, 'tcx> TermVisitor<'tcx> for OpacityVisitor<'a, 'tcx> {
        fn visit_term(&mut self, term: &crate::translation::pearlite::Term<'tcx>) {
            match &term.kind {
                TermKind::Item(id, _) => {
                    if !self.is_visible_enough(*id) {
                        self.error(*id, term.span)
                    }
                }
                TermKind::Call { id, .. } => {
                    if !self.is_visible_enough(*id) {
                        self.error(*id, term.span)
                    }
                }
                TermKind::Constructor { typ, .. } => {
                    if !self.is_visible_enough(*typ) {
                        self.error(*typ, term.span)
                    }
                }
                _ => super_visit_term(term, self),
            }
        }
    }
    if util::is_spec(ctx.tcx, item) {
        return Some(());
    }

    // UGLY clone...
    let term = ctx.term(item)?.clone();

    if ctx.visibility(item) != Visibility::Restricted(parent_module(ctx.tcx, item))
        && util::opacity_witness_name(ctx.tcx, item).is_none()
    {
        ctx.error(ctx.def_span(item), "Non private definitions must have an explicit transparency. Please add #[open(..)] to your definition").emit();
    }

    let opacity = ctx.opacity(item).scope();
    OpacityVisitor { opacity, ctx, source_item: item }.visit_term(&term);
    Some(())
}

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
        ctx.error(sp, "Laws cannot have additional generic parameters").emit();
    }
}

pub(crate) fn validate_impls(ctx: &TranslationCtx) {
    for impl_id in ctx.all_local_trait_impls(()).values().flat_map(|i| i.iter()) {
        if !matches!(ctx.def_kind(*impl_id), DefKind::Impl { .. }) {
            continue;
        }

        let trait_ref = ctx.impl_trait_ref(*impl_id).unwrap().skip_binder();

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
            ctx.error(ctx.def_span(impl_id.to_def_id()), &msg).emit();
        }

        let implementors = ctx.impl_item_implementor_ids(impl_id.to_def_id());

        let implementors =
            ctx.with_stable_hashing_context(|hcx| implementors.to_sorted(&hcx, true));
        for (trait_item, impl_item) in implementors {
            if is_overloaded_item(ctx.tcx, *trait_item) {
                continue;
            };

            let item_type = util::item_type(ctx.tcx, *impl_item);
            let trait_type = util::item_type(ctx.tcx, *trait_item);
            if !item_type.can_implement(trait_type) {
                ctx.error(
                    ctx.def_span(impl_item),
                    &format!(
                        "Expected `{}` to be a {} as specified by the trait declaration",
                        ctx.item_name(*impl_item),
                        trait_type.to_str()
                    ),
                )
                .emit();
            }
        }
    }
}
