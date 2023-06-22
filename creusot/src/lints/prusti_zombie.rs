use crate::translation::pearlite::prusti;
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_session::{declare_tool_lint, impl_lint_pass};

declare_tool_lint! {
    /// Blah Blah
    pub creusot::PRUSTI_ZOMBIE,
    Allow,
    "prusti::zombie"
}

pub struct PrustiZombie {}

impl_lint_pass!(PrustiZombie => [PRUSTI_ZOMBIE]);

impl<'tcx> LateLintPass<'tcx> for PrustiZombie {
    fn check_expr_post(&mut self, cx: &LateContext<'tcx>, expr: &'tcx rustc_hir::Expr<'tcx>) {
        let span = expr.span;
        let data = span.data();
        let error = prusti::ZOMBIE_SPANS.lock().unwrap().get(&data).cloned();
        if let Some(error) = error {
            cx.struct_span_lint(PRUSTI_ZOMBIE, span, &*error, |lint| lint);
        }
    }
}
