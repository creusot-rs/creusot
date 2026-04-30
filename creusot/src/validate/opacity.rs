use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{PlaceTy, ProjectionElem},
    thir::{self, Thir, visit::Visitor},
    ty::{self, TyKind},
};
use rustc_span::Span;

use crate::{
    backend::{is_trusted_item, projections::iter_projections_ty},
    contracts_items::{is_logic, is_opaque},
    ctx::{HasTyCtxt, Opacity, TranslationCtx},
    translation::pearlite::{
        Pattern, PatternKind, Scoped, Term, TermKind,
        visit::{TermVisitor, super_visit_pattern, super_visit_term},
    },
};

struct OpacityVisitor<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    opacity: Opacity,
    item: DefId,
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
            &TermKind::Item(id, _) => {
                if let TyKind::FnDef(_, _) = self.ctx.type_of(id).skip_binder().kind() {
                    return;
                }
                if matches!(self.ctx.def_kind(id), DefKind::ConstParam) {
                    return;
                }
                if !self.is_visible_enough(id) {
                    self.error(id, term.span)
                }
            }
            &TermKind::Call { id, .. } => {
                if !self.is_visible_enough(id) {
                    self.error(id, term.span)
                }
            }
            &TermKind::Constructor { variant, .. } => {
                if let Some(adt) = term.ty.ty_adt_def() {
                    if !self.is_visible_enough(adt.did()) {
                        self.error(adt.did(), term.span);
                    }
                    for fld in &adt.variant(variant).fields {
                        if !self.is_visible_enough(fld.did) {
                            self.error(fld.did, term.span);
                        }
                    }
                }
            }
            &TermKind::Projection { idx, ref lhs } => {
                if let Some(adt) = lhs.ty.ty_adt_def() {
                    let fdid = adt.non_enum_variant().fields[idx].did;
                    if !self.is_visible_enough(fdid) {
                        self.error(fdid, term.span);
                    }
                }
            }
            &TermKind::Reborrow { ref projections, ref inner } => {
                let ty = inner.ty.builtin_deref(false).unwrap();
                for (elem, place_ty) in
                    iter_projections_ty(self.ctx, projections, &mut PlaceTy::from_ty(ty))
                {
                    match elem {
                        ProjectionElem::Field(field_idx, _) => {
                            if let Some(adt) = place_ty.ty.ty_adt_def()
                                && adt.is_struct()
                            {
                                let fdid = adt.non_enum_variant().fields[*field_idx].did;
                                if !self.is_visible_enough(fdid) {
                                    self.error(fdid, term.span);
                                }
                            }
                        }
                        ProjectionElem::Deref | ProjectionElem::Index(_) => (),
                        _ => unreachable!(),
                    }
                }
            }
            &TermKind::Assert { .. } => return, /* Body of proof_assert is not visible from outside */
            _ => (),
        }
        super_visit_term(term, self);
    }

    fn visit_pattern(&mut self, pat: &Pattern<'tcx>) {
        match &pat.kind {
            PatternKind::Constructor(variant_idx, patterns) => {
                let fields_def = &pat.ty.ty_adt_def().unwrap().variants()[*variant_idx].fields;
                for (fld, _) in patterns {
                    let fdid = fields_def[*fld].did;
                    if !self.is_visible_enough(fdid) {
                        self.error(fdid, pat.span);
                    }
                }
            }
            _ => (),
        }
        super_visit_pattern(pat, self);
    }
}

/// Forbid use of opaque type constructors and fields
struct NoOpaqueTypeAccess<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    thir: &'a Thir<'tcx>,
}

impl TranslationCtx<'_> {
    fn assert_non_opaque_ty(&self, ty: ty::Ty, span: Span, desc: &str) {
        if let &TyKind::Adt(adt_def, _) = ty.kind() {
            self.assert_non_opaque_adt(adt_def, span, desc)
        }
    }

    fn assert_non_opaque_adt(&self, adt_def: ty::AdtDef, span: Span, desc: &str) {
        if is_opaque(self.tcx, adt_def.did()) {
            self.error(
                span,
                format!("Forbidden {desc} of opaque type `{}`", self.def_path_str(adt_def.did())),
            )
            .with_help("Only `#[trusted]` program functions can see through opaque types")
            .emit();
        }
    }
}

impl<'thir, 'tcx> Visitor<'thir, 'tcx> for NoOpaqueTypeAccess<'thir, 'tcx> {
    fn thir(&self) -> &'thir Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir thir::Expr<'tcx>) {
        match expr.kind {
            thir::ExprKind::Field { lhs, .. } => {
                self.ctx.assert_non_opaque_ty(self.thir()[lhs].ty, expr.span, "field access")
            }
            thir::ExprKind::Adt(ref constr) => {
                self.ctx.assert_non_opaque_adt(constr.adt_def, expr.span, "constructor")
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'thir thir::Pat<'tcx>) {
        match pat.kind {
            thir::PatKind::Variant { adt_def, .. } => {
                self.ctx.assert_non_opaque_adt(adt_def, pat.span, "constructor")
            }
            thir::PatKind::Leaf { .. } => {
                self.ctx.assert_non_opaque_ty(pat.ty, pat.span, "constructor")
            }
            _ => {}
        }
        thir::visit::walk_pat(self, pat);
    }
}

/// Validates that a private function is not made visible in a public one which is open.
pub(crate) fn validate_opacity<'tcx>(ctx: &TranslationCtx<'tcx>, item: DefId) {
    let is_logic = is_logic(ctx.tcx, item);
    // Forbid use of opaque type constructors and fields, except in trusted program functions
    if is_logic || !is_trusted_item(ctx.tcx, item) {
        let (thir, expr) = ctx.thir_body(item.expect_local());
        let thir = &thir.borrow();
        NoOpaqueTypeAccess { ctx, thir }.visit_expr(&thir[expr]);
    }
    if is_logic && !is_opaque(ctx.tcx, item) {
        let Some(Scoped(_, term)) = ctx.term(item) else { return };
        OpacityVisitor { opacity: *ctx.opacity(item), ctx, item }.visit_term(term);
    }
    let contract = &ctx.sig(item).contract;
    // We consider variants as private, because we don't support mutual recursion for now
    for term in contract.requires.iter().map(|cond| &cond.term).chain(
        contract
            .ensures
            .iter()
            .flat_map(|req| std::iter::once(&req.1.term).chain(req.0.iter().flat_map(|t| &t.0))),
    ) {
        let opacity = Opacity::Transparent(ctx.visibility(item));
        OpacityVisitor { opacity, ctx, item }.visit_term(term);
    }
}
