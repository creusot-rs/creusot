use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::ty::TyCtxt;
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::{Symbol, DUMMY_SP};

declare_tool_lint! {
    /// Blah Blah
    pub creusot::RESOLVE_TRAIT,
    Warn,
    "checks if `creusot_contracts` is available in Creusot code"
}

pub struct ResolveTrait {}

impl_lint_pass!(ResolveTrait => [RESOLVE_TRAIT]);

fn resolve_trait_loaded(tcx: TyCtxt) -> bool {
    tcx.get_diagnostic_item(Symbol::intern("creusot_resolve")).is_some()
}

impl<'tcx> LateLintPass<'tcx> for ResolveTrait {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
        if !resolve_trait_loaded(cx.tcx) {
            cx.opt_span_lint(
                RESOLVE_TRAIT,
                Some(DUMMY_SP),
                |lint| {
                    lint.primary_message("the `creusot_contracts` crate is not loaded. You will not be able to verify any code using Creusot until you do so.");
                },
            );
        }
    }
}
