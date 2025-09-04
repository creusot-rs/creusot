use crate::{contracts_items::is_namespaces_new, ctx::TranslationCtx};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    thir::{self, ExprId, ExprKind, Thir, visit::Visitor},
    ty::{TyCtxt, TyKind},
};
use rustc_span::Span;

pub(crate) fn validate_namespaces_new<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    &(ref thir, expr): &(Thir<'tcx>, ExprId),
) {
    let mut in_main = false;
    if let Some((main_did, _)) = ctx.entry_fn(()) {
        in_main = def_id == main_did;
    }
    NamespacesNewVisitor { tcx: ctx.tcx, thir, in_main, in_loop: false, already_called: None }
        .visit_expr(&thir[expr]);
}

struct NamespacesNewVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
    in_main: bool,
    in_loop: bool,
    already_called: Option<Span>,
}

impl<'a, 'tcx> Visitor<'a, 'tcx> for NamespacesNewVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a thir::Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call { fun, .. } => {
                if let &TyKind::FnDef(func_did, _) = self.thir[fun].ty.kind()
                    && is_namespaces_new(self.tcx, func_did)
                {
                    if !self.in_main {
                        self.tcx.dcx().span_err(
                            expr.span,
                            format!(
                                "{} can only be called in `main`",
                                self.tcx.def_path_str(func_did)
                            ),
                        );
                    } else if self.in_loop {
                        self.tcx.dcx().span_err(
                            expr.span,
                            format!(
                                "{} cannot be called in a loop",
                                self.tcx.def_path_str(func_did)
                            ),
                        );
                    } else if let Some(span) = self.already_called {
                        self.tcx
                            .dcx()
                            .struct_span_err(
                                expr.span,
                                format!(
                                    "{} can only be called once",
                                    self.tcx.def_path_str(func_did)
                                ),
                            )
                            .with_span_note(span, "already called here")
                            .emit();
                    } else {
                        self.already_called = Some(expr.span)
                    }
                }
            }
            ExprKind::Loop { .. } => {
                self.in_loop = true;
                thir::visit::walk_expr(self, expr);
                self.in_loop = false;
                return;
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr)
    }
}
