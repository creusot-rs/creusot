use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{ProjectionElem, tcx::PlaceTy},
    ty::{TyKind, TypingEnv},
};
use rustc_span::Span;
use rustc_target::abi::VariantIdx;

use crate::{
    backend::projections::iter_projections_ty,
    contracts_items::is_spec,
    ctx::{HasTyCtxt, Opacity, TranslationCtx},
    translation::pearlite::{
        Pattern, PatternKind, ScopedTerm, Term, TermKind, TermVisitor, super_visit_pattern,
        super_visit_term,
    },
};

/// Validates that an `#[open]` function is not made visible in a less opened one.
pub(crate) fn validate_opacity(ctx: &TranslationCtx, item: DefId) {
    struct OpacityVisitor<'a, 'tcx> {
        ctx: &'a TranslationCtx<'tcx>,
        opacity: Opacity,
        item: DefId,
        typing_env: TypingEnv<'tcx>,
    }

    impl OpacityVisitor<'_, '_> {
        fn is_visible_enough(&self, id: DefId) -> bool {
            self.ctx.visibility(id).is_at_least(self.opacity.0, self.ctx.tcx)
        }

        fn error(&self, id: DefId, span: Span) {
            self.ctx.error(
                span,
                &format!(
                    "Cannot make `{:?}` transparent in `{:?}` as it would call a less-visible item.",
                    self.ctx.def_path_str(id), self.ctx.def_path_str(self.item)
                ),
            ).emit();
        }
    }

    impl<'tcx> TermVisitor<'tcx> for OpacityVisitor<'_, 'tcx> {
        fn visit_term(&mut self, term: &Term<'tcx>) {
            match &term.kind {
                TermKind::Item(id, _) => {
                    if let TyKind::FnDef(_, _) = self.ctx.type_of(id).skip_binder().kind() {
                        return;
                    }
                    if !self.is_visible_enough(*id) {
                        self.error(*id, term.span)
                    }
                }
                TermKind::Call { id, .. } => {
                    if !self.is_visible_enough(*id) {
                        self.error(*id, term.span)
                    }
                }
                TermKind::Constructor { variant, .. } => {
                    let ty = self.ctx.normalize_erasing_regions(self.typing_env, term.ty);
                    let Some(adt) = ty.ty_adt_def() else { return };
                    if !self.is_visible_enough(adt.did()) {
                        self.error(adt.did(), term.span);
                        return;
                    }
                    for fld in &adt.variant(*variant).fields {
                        if !fld.vis.is_at_least(self.opacity.0, self.ctx.tcx) {
                            self.error(adt.did(), term.span);
                            return;
                        }
                    }
                }
                TermKind::Projection { idx, lhs } => {
                    let ty = self.ctx.normalize_erasing_regions(self.typing_env, lhs.ty);
                    let Some(adt) = ty.ty_adt_def() else { return };
                    let fld = &adt.non_enum_variant().fields[*idx];
                    if !fld.vis.is_at_least(self.opacity.0, self.ctx.tcx) {
                        self.error(fld.did, term.span);
                        return;
                    }
                }
                TermKind::Reborrow { projections, inner } => {
                    let ty = self.ctx.normalize_erasing_regions(self.typing_env, inner.ty);
                    let ty = ty.builtin_deref(false).unwrap();
                    for (elem, place_ty) in
                        iter_projections_ty(self.ctx.tcx, projections, &mut PlaceTy::from_ty(ty))
                    {
                        match elem {
                            ProjectionElem::Field(field_idx, _) => {
                                let Some(adt) = place_ty.ty.ty_adt_def() else { return };
                                let fld = &adt
                                    .variant(place_ty.variant_index.unwrap_or(VariantIdx::ZERO))
                                    .fields[*field_idx];
                                if !fld.vis.is_at_least(self.opacity.0, self.ctx.tcx) {
                                    self.error(fld.did, term.span);
                                    return;
                                }
                            }
                            ProjectionElem::Deref | ProjectionElem::Index(_) => (),
                            _ => unreachable!(),
                        }
                    }
                }
                TermKind::Assert { .. } => return,
                _ => (),
            }
            super_visit_term(term, self);
        }

        fn visit_pattern(&mut self, pat: &Pattern<'tcx>) {
            match &pat.kind {
                PatternKind::Constructor(variant_idx, patterns) => {
                    let ty = self.ctx.normalize_erasing_regions(self.typing_env, pat.ty);
                    let fields_def = &ty.ty_adt_def().unwrap().variants()[*variant_idx].fields;
                    for (fld, _) in patterns {
                        let fld = &fields_def[*fld];
                        if !fld.vis.is_at_least(self.opacity.0, self.ctx.tcx) {
                            self.error(fld.did, pat.span);
                            return;
                        }
                    }
                }
                _ => (),
            }
            super_visit_pattern(pat, self);
        }
    }

    if is_spec(ctx.tcx, item) {
        return;
    }

    let Some(ScopedTerm(_, term)) = ctx.term(item) else { return };
    let typing_env = ctx.typing_env(item);
    OpacityVisitor { opacity: *ctx.opacity(item), ctx, item, typing_env }.visit_term(term);
}
