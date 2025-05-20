use crate::*;
use ::std::marker::PhantomData;

/// A unique id, usable in logic
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
