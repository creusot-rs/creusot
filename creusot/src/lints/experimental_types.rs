use rustc_hir::Expr;
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::{lint::in_external_macro, ty};
use rustc_session::{declare_tool_lint, impl_lint_pass};

declare_tool_lint! {
    /// Blah Blah
    pub creusot::EXPERIMENTAL,
    Warn,
    "using Rust features that only have basic or experimental support in Creusot"
}

pub struct Experimental {}

impl_lint_pass!(Experimental => [EXPERIMENTAL]);

fn is_dyn_ty(cx: &LateContext<'_>, e: &Expr<'_>) -> bool {
    match cx.typeck_results().expr_ty(e).peel_refs().kind() {
        ty::Dynamic(_, _, _) => true,
        _ => false,
    }
}

impl<'tcx> LateLintPass<'tcx> for Experimental {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, e: &'tcx rustc_hir::Expr<'tcx>) {
        if in_external_macro(cx.sess(), e.span) {
            return;
        }
        // This is necessary because the string generated by `assert!` has no span and thus 'is not' in an external macro.
        let parent = cx.tcx.hir().parent_id_iter(e.hir_id).next().unwrap();
        if in_external_macro(cx.sess(), cx.tcx.hir().span(parent)) {
            return;
        }

        if is_dyn_ty(cx, e) {
            cx.opt_span_lint(EXPERIMENTAL, Some(e.span), |lint| {
                lint.primary_message("support for trait objects (dyn) is limited and experimental");
            });
        }
    }
}
