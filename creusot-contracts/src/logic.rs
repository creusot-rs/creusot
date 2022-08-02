#![allow(unused_imports)]
mod fset;
#[cfg(feature = "contracts")]
mod ghost;
mod int;
mod mapping;
mod model;
pub mod ord;
mod resolve;
mod seq;
mod set;
pub mod well_founded;

#[cfg(not(feature = "contracts"))]
pub mod ghost {
    pub struct Ghost<T>(std::marker::PhantomData<T>)
    where
        T: ?Sized;

    impl<T> Ghost<T> {
        pub fn new() -> Ghost<T> {
            Ghost(std::marker::PhantomData)
        }
    }
}

pub use fset::*;
pub use ghost::*;
pub use int::*;
pub use mapping::*;
pub use model::*;
pub use ord::*;
pub use resolve::*;
pub use seq::*;
pub use set::*;
pub use well_founded::*;
