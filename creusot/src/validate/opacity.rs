use rustc_abi::VariantIdx;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{PlaceTy, ProjectionElem},
    ty::{TyKind, TypingEnv},
};
use rustc_span::Span;

use crate::{
    backend::projections::iter_projections_ty,
    contracts_items::{is_logic, is_opaque},
    ctx::{HasTyCtxt, Opacity, TranslationCtx},
    translation::pearlite::{
        Pattern, PatternKind, ScopedTerm, Term, TermKind, TermVisitor, super_visit_pattern,
        super_visit_term,
    },
};

struct OpacityVisitor<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    opacity: Opacity,
    item: DefId,
    typing_env: TypingEnv<'tcx>,
}

impl OpacityVisitor<'_, '_> {
    fn is_visible_enough(&self, id: DefId) -> bool {
        let Opacity::Transparent(op) = self.opacity else { return true };
        self.ctx.visibility(id).is_at_least(op, self.ctx.tcx)
    }

    fn error(&self, id: DefId, span: Span) {
        self.ctx.error(
                span,
                format!(
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
                if matches!(self.ctx.def_kind(*id), DefKind::ConstParam) {
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
                    if !self.is_visible_enough(fld.did) {
                        self.error(fld.did, term.span);
                        return;
                    }
                }
            }
            TermKind::Projection { idx, lhs } => {
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, lhs.ty);
                let Some(adt) = ty.ty_adt_def() else { return };
                let fdid = adt.non_enum_variant().fields[*idx].did;
                if !self.is_visible_enough(fdid) {
                    self.error(fdid, term.span);
                    return;
                }
            }
            TermKind::Reborrow { projections, inner } => {
                let ty = self.ctx.normalize_erasing_regions(self.typing_env, inner.ty);
                let ty = ty.builtin_deref(false).unwrap();
                for (elem, place_ty) in
                    iter_projections_ty(self.ctx, projections, &mut PlaceTy::from_ty(ty))
                {
                    match elem {
                        ProjectionElem::Field(field_idx, _) => {
                            let Some(adt) = place_ty.ty.ty_adt_def() else { return };
                            let fdid = adt
                                .variant(place_ty.variant_index.unwrap_or(VariantIdx::ZERO))
                                .fields[*field_idx]
                                .did;
                            if !self.is_visible_enough(fdid) {
                                self.error(fdid, term.span);
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
                    let fdid = fields_def[*fld].did;
                    if !self.is_visible_enough(fdid) {
                        self.error(fdid, pat.span);
                        return;
                    }
                }
            }
            _ => (),
        }
        super_visit_pattern(pat, self);
    }
}

/// Validates that a private function is not made visible in a public one which is open.
pub(crate) fn validate_opacity<'tcx>(ctx: &TranslationCtx<'tcx>, item: DefId) {
    let typing_env = ctx.typing_env(item);
    if is_logic(ctx.tcx, item) && !is_opaque(ctx.tcx, item) {
        let Some(ScopedTerm(_, term)) = ctx.term(item) else { return };
        OpacityVisitor { opacity: *ctx.opacity(item), ctx, item, typing_env }.visit_term(term);
    }
    let contract = &ctx.sig(item).contract;
    // We consider variants as private, because we don't support mutual recursion for now
    for term in contract.requires.iter().chain(contract.ensures.iter()).map(|cond| &cond.term) {
        let opacity = Opacity::Transparent(ctx.visibility(item));
        OpacityVisitor { opacity, ctx, item, typing_env }.visit_term(term);
    }
}
