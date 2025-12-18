use crate::{logic::ops::IndexLogic, prelude::*};
use core::marker::PhantomData;

/// A mapping: map every value of type `A` to a value of type `B`.
///
/// # Pearlite syntax
///
/// Mappings have special support in pearlite code: you may write a closure to create a
/// mapping.
///
/// ## Example
///
/// ```
/// # use creusot_contracts::{logic::Mapping, prelude::*};
/// let value = snapshot!(4);
/// let map: Snapshot<Mapping<Int, Int>> = snapshot!(|n| if n % 2 == 0 { 0 } else { *value });
/// proof_assert!(map.get(1) == 4);
/// ```
#[builtin("map.Map.map")]
pub struct Mapping<A: ?Sized, B>(PhantomData<A>, PhantomData<B>);

impl<A: ?Sized, B> Mapping<A, B> {
    /// Get the value associated with `a` in the map.
    #[logic]
    #[builtin("map.Map.get")]
    #[allow(unused_variables)]
    pub fn get(self, a: A) -> B {
        dead
    }

    /// Returns a new mapping, where `a` is now mapped to `b`.
    #[logic]
    #[builtin("map.Map.set")]
    #[allow(unused_variables)]
    pub fn set(self, a: A, b: B) -> Self {
        dead
    }

    /// Create a mapping, where every value of type `a` is mapped to `b`.
    #[logic]
    #[builtin("map.Const.const")]
    #[allow(unused_variables)]
    pub fn cst(b: B) -> Self {
        dead
    }

    /// Extensional equality.
    ///
    /// Returns `true` if `self` and `other` contain exactly the same key-value pairs.
    ///
    /// This is in fact equivalent with normal equality.
    #[logic]
    #[builtin("map.MapExt.(==)")]
    #[allow(unused_variables)]
    pub fn ext_eq(self, x: Self) -> bool {
        dead
    }
}

impl<A: ?Sized, B> IndexLogic<A> for Mapping<A, B> {
    type Item = B;

    #[logic(open, inline)]
    fn index_logic(self, a: A) -> B {
        self.get(a)
    }
}
