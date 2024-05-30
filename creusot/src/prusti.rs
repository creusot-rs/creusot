mod parsing;
pub(crate) mod typeck;
pub(crate) use typeck::check_signature_agreement;
mod bitvec;
pub(crate) mod ctx;
mod flat_rust_ty;
mod flat_ty;
mod fn_sig_binder;
mod region_set;
mod sig;
pub(crate) mod types;
mod util;
mod variance;
mod zombie;

pub(crate) use fn_sig_binder::FnSigBinder;
pub(crate) use region_set::State;
pub(crate) use sig::{full_signature, full_signature_logic};
