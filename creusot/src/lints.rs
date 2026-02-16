mod contractless_external_function;
mod experimental_types;
mod trusted;

use rustc_lint::LintStore;
use rustc_macros::LintDiagnostic;
use rustc_session::Session;
use rustc_span::{Span, Symbol};

pub(crate) use contractless_external_function::CONTRACTLESS_EXTERNAL_FUNCTION;

use crate::validate;

// Diagnostics for creusot's lints.
//
// This only describes the structure of the diagnostics. The actual messages
// are defined in `creusot/messages.ftl`
#[derive(Debug, LintDiagnostic)]
pub(crate) enum Diagnostics {
    #[diag("used the `#[trusted]` attribute")]
    TrustedAttribute,
    /// Usually lints are emitted by implementing lint passes with the `impl_lint_pass!` macro.
    ///
    /// Since the lint is emmited at a "weird" time (during translation to
    /// fmir), we cannot do this, so this structure will be used with the
    /// `TyCtxt::emit_node_span_lint` function.
    #[diag("calling external function `{$name}` with no contract will yield an impossible precondition")]
    ContractlessExternalFunction {
        /// Name of the function
        name: Symbol,
        /// Location of the call
        #[label("function called here")]
        span: Span,
    },
    #[diag("support for trait objects (dyn) is limited and experimental")]
    DynExperimental,
}

pub fn register_lints(_sess: &Session, store: &mut LintStore) {
    store.register_lints(&[
        experimental_types::EXPERIMENTAL,
        contractless_external_function::CONTRACTLESS_EXTERNAL_FUNCTION,
        trusted::TRUSTED_CODE,
    ]);
    store.register_late_pass(move |_| Box::new(validate::GhostValidate {}));
    store.register_late_pass(move |_| Box::new(experimental_types::Experimental {}));
    store.register_late_pass(move |_| Box::new(trusted::TrustedCode {}));
}
