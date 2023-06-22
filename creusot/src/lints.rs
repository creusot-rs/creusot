mod experimental_types;
mod prusti_zombie;
mod resolve_trait;

pub fn register_lints(_sess: &Session, store: &mut LintStore) {
    store.register_lints(&[EXPERIMENTAL, RESOLVE_TRAIT, PRUSTI_ZOMBIE]);
    store.register_late_pass(move |_| Box::new(experimental_types::Experimental {}));
    store.register_late_pass(move |_| Box::new(resolve_trait::ResolveTrait {}));
}

use rustc_lint::LintStore;
use rustc_session::Session;

pub(crate) use self::{
    experimental_types::EXPERIMENTAL, prusti_zombie::PRUSTI_ZOMBIE, resolve_trait::RESOLVE_TRAIT,
};
