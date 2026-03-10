mod contractless_external_function;
mod experimental_types;
mod result_param;
mod trusted;

use rustc_lint::LintStore;
use rustc_macros::Diagnostic;
use rustc_session::Session;
use rustc_span::{Span, Symbol};

pub(crate) use contractless_external_function::CONTRACTLESS_EXTERNAL_FUNCTION;
pub(crate) use result_param::RESULT_PARAM;

use crate::validate;

// Diagnostics for creusot's lints.
#[derive(Debug, Diagnostic)]
pub(crate) enum Diagnostics {
    #[diag("used the `#[trusted]` attribute")]
    TrustedAttribute,
    /// Usually lints are emitted by implementing lint passes with the `impl_lint_pass!` macro.
    ///
    /// Since the lint is emmited at a "weird" time (during translation to
    /// fmir), we cannot do this, so this structure will be used with the
    /// `TyCtxt::emit_node_span_lint` function.
    #[diag(
        "calling external function `{$name}` with no contract will yield an impossible precondition"
    )]
    ContractlessExternalFunction {
        /// Name of the function
        name: Symbol,
        /// Location of the call
        #[label("function called here")]
        span: Span,
    },
    #[diag("support for trait objects (dyn) is limited and experimental")]
    DynExperimental,
    #[diag(
        "`result` used as a parameter name. It is confusing because it is also the default name of the function's result"
    )]
    ResultParam,
}

pub fn register_lints(_sess: &Session, store: &mut LintStore) {
    store.register_lints(&[
        experimental_types::EXPERIMENTAL,
        contractless_external_function::CONTRACTLESS_EXTERNAL_FUNCTION,
        trusted::TRUSTED_CODE,
        result_param::RESULT_PARAM,
    ]);
    store.register_late_pass(move |_| Box::new(validate::GhostValidate {}));
    store.register_late_pass(move |_| Box::new(experimental_types::Experimental {}));
    store.register_late_pass(move |_| Box::new(trusted::TrustedCode {}));
}
