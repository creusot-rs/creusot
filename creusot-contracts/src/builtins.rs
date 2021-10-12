use crate as creusot_contracts;
use creusot_contracts_proc::*;

mod int;
mod seq;
pub use int::*;
pub use seq::*;

pub trait Model {
    type ModelTy;
    #[logic_rust]
    fn model(self) -> Self::ModelTy;
}

#[rustc_diagnostic_item = "creusot_resolve"]
pub unsafe trait Resolve {
    #[predicate_rust]
    #[rustc_diagnostic_item = "creusot_resolve_method"]
    fn resolve(self) -> bool;
}

unsafe impl<T1: Resolve, T2: Resolve> Resolve for (T1, T2) {
    #[predicate_rust]
    fn resolve(self) -> bool {
        Resolve::resolve(self.0) && Resolve::resolve(self.1)
    }
}

unsafe impl<T> Resolve for &mut T {
    predicate! {
        fn resolve(self) -> bool {
            ^self === *self
        }
    }
}
