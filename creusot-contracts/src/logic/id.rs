use crate::{ghost::Plain, prelude::*};

/// A unique id, usable in logic and ghost code
///
/// The only properties of this type are:
/// - there is an infinite number of ids
/// - You can always generate a fresh id in logic code
///
/// # Usage
///
/// Ids are used in [`cell::PermCell`] and [resource algebras](crate::ghost::resource::Resource).
#[opaque]
#[allow(dead_code)]
pub struct Id(());

impl Clone for Id {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}
impl Copy for Id {}

#[trusted]
impl Plain for Id {}

impl PartialEq for Id {
    #[trusted]
    #[check(ghost)]
    #[ensures(result == (*self == *other))]
    #[allow(unused_variables)]
    fn eq(&self, other: &Self) -> bool {
        panic!()
    }

    #[check(ghost)]
    #[ensures(result != (*self == *other))]
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}
impl Eq for Id {}

impl DeepModel for Id {
    type DeepModelTy = Id;
    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}
