use rustc_hir::def_id::DefId;
use rustc_middle::ty::Visibility;
use rustc_span::Span;

use crate::{
    contracts_items::{is_spec, opacity_witness_name},
    ctx::TranslationCtx,
    translation::pearlite::{ScopedTerm, TermKind, TermVisitor, super_visit_term},
    util::parent_module,
};

/// Validates that an `#[open]` function is not made visible in a less opened one.
pub(crate) fn validate_opacity(ctx: &TranslationCtx, item: DefId) {
    struct OpacityVisitor<'a, 'tcx> {
        ctx: &'a TranslationCtx<'tcx>,
        opacity: Option<DefId>,
        source_item: DefId,
    }

    impl OpacityVisitor<'_, '_> {
        fn is_visible_enough(&self, id: DefId) -> bool {
            match self.opacity {
                None => self.ctx.visibility(id) == Visibility::Public,
                Some(opa) => self.ctx.visibility(id).is_accessible_from(opa, self.ctx.tcx),
            }
        }

        fn error(&self, id: DefId, span: Span) {
            self.ctx.error(
                span,
                &format!(
                    "Cannot make `{:?}` transparent in `{:?}` as it would call a less-visible item.",
                    self.ctx.def_path_str(id), self.ctx.def_path_str(self.source_item)
                ),
            ).emit();
        }
    }

    impl<'tcx> TermVisitor<'tcx> for OpacityVisitor<'_, 'tcx> {
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

    if is_spec(ctx.tcx, item) {
        return;
    }

    let Some(ScopedTerm(_, term)) = ctx.term(item) else { return };

    if ctx.visibility(item) != Visibility::Restricted(parent_module(ctx.tcx, item))
        && opacity_witness_name(ctx.tcx, item).is_none()
    {
        ctx.error(ctx.def_span(item), "Non private definitions must have an explicit transparency. Please add #[open(..)] to your definition").emit();
    }

    let opacity = ctx.opacity(item).scope();
    OpacityVisitor { opacity, ctx, source_item: item }.visit_term(term);
}
