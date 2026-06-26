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
    ctx::{HasTyCtxt, ItemType, Opacity, TranslationCtx},
    translation::pearlite::{
        Literal, Pattern, PatternKind, Scoped, Term, TermKind,
        visit::{TermVisitor, super_visit_pattern, super_visit_term},
    },
};

struct OpacityVisitor<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    opacity: Opacity,
    item: DefId,
}

impl OpacityVisitor<'_, '_> {
    /// Assert that `id` is visible from the body of `self.item` with opacity `self.opacity`.
    fn assert_visible(&self, id: DefId, span: Span) {
        if !self.is_visible(id) {
            self.error(id, span)
        }
    }

    fn is_visible(&self, id: DefId) -> bool {
        use std::cmp::Ordering::{Equal, Greater};
        let Opacity::Transparent(self_vis) = self.opacity else { return true };
        matches!(self.ctx.visibility(id).partial_cmp(self_vis, self.ctx.tcx), Some(Greater | Equal))
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
            TermKind::Let {
                pattern: Pattern { kind: PatternKind::Wildcard, .. },
                arg: box Term { kind: TermKind::Lit(Literal::ZST), .. },
                ..
            } => {
                // Do not check the visibility in "let _ = <function literal>" because it is a
                // common pattern for proof hints.
                return;
            }
            TermKind::Lit(Literal::ZST) if let &TyKind::FnDef(id, _) = term.ty.kind() => {
                self.assert_visible(id, term.span)
            }
            &TermKind::ConstItem { id, .. }
                if !matches!(self.ctx.def_kind(id), DefKind::ConstParam) =>
            {
                self.assert_visible(id, term.span)
            }
            &TermKind::Call { id, .. } => self.assert_visible(id, term.span),
            &TermKind::Constructor { variant, .. } => {
                if let Some(adt) = term.ty.ty_adt_def() {
                    self.assert_visible(adt.did(), term.span);
                    for fld in &adt.variant(variant).fields {
                        self.assert_visible(fld.did, term.span);
                    }
                }
            }
            &TermKind::Projection { idx, ref lhs } => {
                if let Some(adt) = lhs.ty.ty_adt_def() {
                    let fdid = adt.non_enum_variant().fields[idx].did;
                    self.assert_visible(fdid, term.span);
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

                                self.assert_visible(fdid, term.span);
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
                    self.assert_visible(fdid, pat.span);
                }
            }
            _ => (),
        }
        super_visit_pattern(pat, self);
    }
}

/// Opacity check in THIR. Check two things:
/// 1. Forbid use of opaque type constructors and fields (in logic and non-trusted program definitions)
/// 2. In consts and logic functions, forbid use of less visible constructors, and fields (`opacity` is `Some`).
struct ThirOpacityVisitor<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    thir: &'a Thir<'tcx>,
    opacity: Option<Opacity>,
    item_type: ItemType,
    /// The item being visited, for error reporting
    item: DefId,
}

impl<'a, 'tcx> ThirOpacityVisitor<'a, 'tcx> {
    fn visible_body(&self) -> bool {
        matches!(self.item_type, ItemType::Constant)
    }

    fn is_logic(&self) -> bool {
        matches!(self.item_type, ItemType::Logic { .. })
    }

    fn assert_non_opaque_adt(&self, adt_def: ty::AdtDef, span: Span, desc: &str) {
        if is_opaque(self.ctx.tcx, adt_def.did()) {
            self.ctx
                .error(
                    span,
                    format!(
                        "Forbidden {desc} of opaque type `{}`",
                        self.ctx.def_path_str(adt_def.did())
                    ),
                )
                .with_help("Only `#[trusted]` program functions can see through opaque types")
                .emit();
        }
    }

    fn assert_visible(&self, id: DefId, span: Span) {
        if !self.is_visible(id) {
            self.error(id, span)
        }
    }

    fn is_visible(&self, id: DefId) -> bool {
        use std::cmp::Ordering::{Equal, Greater};
        let Some(Opacity::Transparent(self_vis)) = self.opacity else { return true };
        matches!(self.ctx.visibility(id).partial_cmp(self_vis, self.ctx.tcx), Some(Greater | Equal))
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

impl<'thir, 'tcx> Visitor<'thir, 'tcx> for ThirOpacityVisitor<'thir, 'tcx> {
    fn thir(&self) -> &'thir Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir thir::Expr<'tcx>) {
        match expr.kind {
            thir::ExprKind::Field { lhs, variant_index, name }
                if let Some(adt_def) = self.thir[lhs].ty.ty_adt_def() =>
            {
                self.assert_non_opaque_adt(adt_def, expr.span, "field access");
                if self.visible_body() {
                    let fdid = adt_def.variant(variant_index).fields[name].did;
                    self.assert_visible(fdid, expr.span);
                }
            }
            thir::ExprKind::Adt(ref constr) => {
                self.assert_non_opaque_adt(constr.adt_def, expr.span, "constructor");
                if self.visible_body() {
                    self.assert_visible(constr.adt_def.did(), expr.span);
                    for fld in &constr.adt_def.variant(constr.variant_index).fields {
                        self.assert_visible(fld.did, expr.span);
                    }
                }
            }
            thir::ExprKind::Call { ty, .. }
                if self.visible_body()
                    && let &TyKind::FnDef(id, _) = ty.kind() =>
            {
                self.assert_visible(id, expr.span)
            }
            thir::ExprKind::Closure(ref closure_expr) => {} // TODO?
            thir::ExprKind::ZstLiteral { .. }
                if self.visible_body()
                    && let &TyKind::FnDef(id, _) = expr.ty.kind() =>
            {
                self.assert_visible(id, expr.span)
            }
            thir::ExprKind::NamedConst { def_id, .. }
                if self.visible_body()
                    && !matches!(self.ctx.def_kind(def_id), DefKind::ConstParam) =>
            {
                self.assert_visible(def_id, expr.span)
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr);
    }

    fn visit_stmt(&mut self, stmt: &'thir thir::Stmt<'tcx>) {
        // Do not check the visibility of rhs in "let _ = rhs;" because it is only used
        // for proof hints (proof_assert and hack to load lemmas).
        if self.is_logic()
            && matches!(stmt.kind, thir::StmtKind::Let { pattern: box thir::Pat { kind: thir::PatKind::Wild, .. }, .. })
        {
            return;
        }
        thir::visit::walk_stmt(self, stmt);
    }

    fn visit_pat(&mut self, pat: &'thir thir::Pat<'tcx>) {
        match pat.kind {
            thir::PatKind::Variant { adt_def, variant_index, ref subpatterns, .. } => {
                self.assert_non_opaque_adt(adt_def, pat.span, "constructor");
                if self.visible_body() {
                    let variant = adt_def.variant(variant_index);
                    for p in subpatterns {
                        let fdid = variant.fields[p.field].did;
                        self.assert_visible(fdid, pat.span)
                    }
                }
            }
            thir::PatKind::Leaf { ref subpatterns }
                if let &TyKind::Adt(adt_def, _) = pat.ty.kind() =>
            {
                self.assert_non_opaque_adt(adt_def, pat.span, "constructor");
                if self.visible_body() {
                    self.assert_visible(adt_def.did(), pat.span);
                    for p in subpatterns {
                        let fdid = adt_def.non_enum_variant().fields[p.field].did;
                        self.assert_visible(fdid, pat.span);
                    }
                }
            }
            _ => {}
        }
        thir::visit::walk_pat(self, pat);
    }
}

/// Validates that a private function is not made visible in a public one which is open.
pub(crate) fn validate_opacity<'tcx>(ctx: &TranslationCtx<'tcx>, item: DefId) {
    let is_logic = is_logic(ctx.tcx, item);
    let opaque = if is_logic { is_opaque(ctx.tcx, item) } else { is_trusted_item(ctx.tcx, item) };
    if !opaque {
        let (thir, expr) = ctx.thir_body(item.expect_local());
        let thir = &thir.borrow();
        let item_type = ctx.item_type(item);
        let opacity = match item_type {
            ItemType::Constant | ItemType::Logic { .. } => Some(*ctx.opacity(item)),
            _ => None,
        };
        ThirOpacityVisitor { ctx, thir, item, opacity, item_type }.visit_expr(&thir[expr])
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
