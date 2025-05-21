use super::Diagnostics;
use rustc_lint::{LateLintPass, LintContext};
use rustc_session::{declare_lint_pass, declare_tool_lint};

declare_tool_lint! {
    /// The `trusted_code` lint catches usage of `#[trusted]`.
    ///
    /// This lint is useful to ensure that you are not using any additionnal axioms in
    /// your code.
    pub creusot::TRUSTED_CODE,
    Allow,
    "`#[trusted]` adds additionnal unproved axioms",
    report_in_external_macro: true
}

declare_lint_pass!(TrustedCode => [TRUSTED_CODE]);
impl<'tcx> LateLintPass<'tcx> for TrustedCode {
    fn check_attribute(
        &mut self,
        cx: &rustc_lint::LateContext<'tcx>,
        attr: &'tcx rustc_hir::Attribute,
    ) {
        let expected = ["creusot", "decl", "trusted"];
        let is_trusted = match &attr.kind {
            rustc_hir::AttrKind::Normal(item) => {
                let s = &item.path.segments;
                s.len() == expected.len() && s.iter().zip(expected).all(|(a, b)| a.as_str() == b)
            }
            rustc_hir::AttrKind::DocComment { .. } => false,
        };
        if is_trusted {
            cx.emit_span_lint(TRUSTED_CODE, attr.span, Diagnostics::TrustedAttribute);
        }
    }
}
