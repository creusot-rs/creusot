use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    thir::{self, Thir, visit::Visitor},
    ty::{self, TyKind},
};
use rustc_span::Span;

use crate::{
    backend::is_trusted_item,
    contracts_items::{is_logic, is_opaque},
    ctx::{HasTyCtxt, ItemType, Opacity, TranslationCtx},
};

/// Item kind for opacity check
#[derive(Clone, Copy, Debug)]
enum ItemKind {
    Const,
    Logic,
    Program,
}

/// Opacity check in THIR. Check two things:
/// 1. Forbid use of opaque type constructors and fields (in logic and non-trusted program definitions)
/// 2. In consts and logic functions, forbid use of less visible constructors, and fields (`opacity` is `Some`).
struct OpacityVisitor<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    thir: &'a Thir<'tcx>,
    opacity: Option<Opacity>,
    item_kind: ItemKind,
    /// The item being visited, for error reporting
    item: DefId,
}

impl<'a, 'tcx> OpacityVisitor<'a, 'tcx> {
    /// Its body may be exposed in the translation of callers
    fn visible_body(&self) -> bool {
        match self.item_kind {
            ItemKind::Const => true,
            ItemKind::Logic if let Some(Opacity::Transparent(_)) = self.opacity => true,
            _ => false,
        }
    }

    fn is_logic(&self) -> bool {
        matches!(self.item_kind, ItemKind::Logic)
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

impl<'thir, 'tcx> Visitor<'thir, 'tcx> for OpacityVisitor<'thir, 'tcx> {
    fn thir(&self) -> &'thir Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir thir::Expr<'tcx>) {
        use thir::ExprKind::*;
        match expr.kind {
            Field { lhs, variant_index, name }
                if let Some(adt_def) = self.thir[lhs].ty.ty_adt_def() =>
            {
                self.assert_non_opaque_adt(adt_def, expr.span, "field access");
                if self.visible_body() {
                    let fdid = adt_def.variant(variant_index).fields[name].did;
                    self.assert_visible(fdid, expr.span);
                }
            }
            Adt(ref constr) => {
                self.assert_non_opaque_adt(constr.adt_def, expr.span, "constructor");
                if self.visible_body() {
                    self.assert_visible(constr.adt_def.did(), expr.span);
                    for fld in &constr.adt_def.variant(constr.variant_index).fields {
                        self.assert_visible(fld.did, expr.span);
                    }
                }
            }
            Closure(ref closure_expr) => {
                let (thir, expr) = self.ctx.thir_body(closure_expr.closure_id);
                let thir = &thir.borrow();
                use crate::contracts_items::get_creusot_item;
                let is_requires_or_ensures =
                    get_creusot_item(self.ctx.tcx, closure_expr.closure_id.to_def_id()).is_some();
                // Change the opacity for requires and ensures
                // Note: we consider variants as private, because we don't support mutual recursion for now
                let opacity;
                let item_type;
                if is_requires_or_ensures {
                    // opacity = Some(Opacity::Transparent(self.ctx.visibility(self.item)));
                    // item_type = ItemType::Logic { prophetic: true };
                    return; // FIXME: fix derived specs for Clone to not break opacity (#1910, #1672)
                } else {
                    opacity = self.opacity;
                    item_type = self.item_kind;
                }
                OpacityVisitor { thir, opacity, item_kind: item_type, ..*self }
                    .visit_expr(&thir[expr])
            }
            // Functions are handled here
            ZstLiteral { .. }
                if self.visible_body()
                    && let &TyKind::FnDef(id, _) = expr.ty.kind() =>
            {
                self.assert_visible(id, expr.span)
            }
            NamedConst { def_id, .. }
                if self.visible_body()
                    && !matches!(self.ctx.def_kind(def_id), DefKind::ConstParam) =>
            {
                self.assert_visible(def_id, expr.span)
            }
            ConstBlock { did, args: _ } => {
                let (thir, expr) = self.ctx.thir_body(did.expect_local());
                let thir = &thir.borrow();
                OpacityVisitor { thir, ..*self }.visit_expr(&thir[expr]);
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
        use thir::PatKind::*;
        match pat.kind {
            Variant { adt_def, variant_index, ref subpatterns, .. } => {
                self.assert_non_opaque_adt(adt_def, pat.span, "constructor");
                if self.visible_body() {
                    let variant = adt_def.variant(variant_index);
                    for p in subpatterns {
                        let fdid = variant.fields[p.field].did;
                        self.assert_visible(fdid, pat.span)
                    }
                }
            }
            Leaf { ref subpatterns } if let &TyKind::Adt(adt_def, _) = pat.ty.kind() => {
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

/// Validates that a private function is not made visible in a public *open* logic function or in a public const.
pub(crate) fn validate_opacity<'tcx>(ctx: &TranslationCtx<'tcx>, item: DefId) {
    if matches!(ctx.tcx.def_kind(item), DefKind::Closure | DefKind::InlineConst) {
        return;
    }
    let is_logic = is_logic(ctx.tcx, item);
    let opaque = if is_logic { is_opaque(ctx.tcx, item) } else { is_trusted_item(ctx.tcx, item) };
    if !opaque {
        let (thir, expr) = ctx.thir_body(item.expect_local());
        let thir = &thir.borrow();
        let item_kind = match ItemType::from(ctx.item_type(item)) {
            ItemType::Logic { .. } => ItemKind::Logic,
            ItemType::Constant => ItemKind::Const,
            _ => ItemKind::Program,
        };
        let opacity = match item_kind {
            ItemKind::Const | ItemKind::Logic => Some(*ctx.opacity(item)),
            ItemKind::Program => None,
        };
        OpacityVisitor { ctx, thir, item, opacity, item_kind }.visit_expr(&thir[expr])
    }
}
