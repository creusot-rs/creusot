use rustc_macros::LintDiagnostic;
use rustc_session::declare_tool_lint;
use rustc_span::{Span, Symbol};

// Usually lints are emitted by implementing lint passes with the `impl_lint_pass!` macro.
// Here, since the lint is emmited at a "weird" time (during translation to fmir), we
// cannot do this, so this structure will be used with the `TyCtxt::emit_node_span_lint`
// function.
#[derive(Debug, LintDiagnostic)]
#[diag(creusot_contractless_external_function)]
pub(crate) struct ContractlessExternalFunction {
    /// Name of the function
    pub(crate) name: Symbol,
    /// Location of the call
    #[label]
    pub(crate) span: Span,
}

declare_tool_lint! {
    /// The `contractless_external_function` lint warns when calling a function from
    /// another crate that has not been given a specification.
    ///
    /// In this case, creusot will give it an impossible to fulfill specification:
    /// `#[require(false)]`.
    pub(crate) creusot::CONTRACTLESS_EXTERNAL_FUNCTION,
    Warn,
    "No proof that use such a function can be completed"
}
