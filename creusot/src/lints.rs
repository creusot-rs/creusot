pub(crate) mod contractless_external_function;
mod experimental_types;

use rustc_lint::LintStore;
use rustc_session::Session;

pub fn register_lints(_sess: &Session, store: &mut LintStore) {
    store.register_lints(&[
        experimental_types::EXPERIMENTAL,
        contractless_external_function::CONTRACTLESS_EXTERNAL_FUNCTION,
    ]);
    store.register_late_pass(move |_| Box::new(experimental_types::Experimental {}));
}
