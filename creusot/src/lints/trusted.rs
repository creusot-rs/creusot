use super::Diagnostics;
use rustc_hir::Attribute;
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
    fn check_attribute(&mut self, cx: &rustc_lint::LateContext<'tcx>, attr: &'tcx Attribute) {
        let expected = ["creusot", "decl", "trusted"];
        let Attribute::Unparsed(box attr) = attr else { return };
        let s = &attr.path.segments;
        let is_trusted =
            s.len() == expected.len() && s.iter().zip(expected).all(|(a, b)| a.as_str() == b);
        if is_trusted {
            cx.emit_span_lint(TRUSTED_CODE, attr.span, Diagnostics::TrustedAttribute);
        }
    }
}
