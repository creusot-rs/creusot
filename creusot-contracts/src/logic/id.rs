use crate::*;
use ::std::marker::PhantomData;

/// A unique id, usable in logic and ghost code
///
/// The only properties of this type are:
/// - there is an infinite number of ids
/// - You can always generate a fresh id in logic code
///
/// # Usage
///
/// Ids are used in [`pcell`](crate::pcell) and [resource algebras](crate::resource).
#[trusted]
#[allow(dead_code)]
pub struct Id(PhantomData<()>);

impl Clone for Id {
    #[pure]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}
impl Copy for Id {}

impl PartialEq for Id {
    #[trusted]
    #[pure]
    #[ensures(result == (*self == *other))]
    #[allow(unused_variables)]
    fn eq(&self, other: &Self) -> bool {
        unreachable!("BUG: called ghost function in normal code")
    }

    #[pure]
    #[ensures(result != (*self == *other))]
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}
impl Eq for Id {}

impl DeepModel for Id {
    type DeepModelTy = Id;
    #[logic]
    #[open]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}
