use crate::{logic::ops::IndexLogic, *};

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
/// # use creusot_contracts::{logic::Mapping, *};
/// let value = snapshot!(4);
/// let map: Snapshot<Mapping<Int, Int>> = snapshot!(|n| if n % 2 == 0 { 0 } else { *value });
/// proof_assert!(map.get(1) == 4);
/// ```
#[trusted]
#[cfg_attr(creusot, creusot::builtins = "map.Map.map")]
pub struct Mapping<A: ?Sized, B: ?Sized>(std::marker::PhantomData<A>, std::marker::PhantomData<B>);

impl<A: ?Sized, B: ?Sized> Mapping<A, B> {
    /// Get the value associated with `a` in the map.
    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Map.get"]
    #[allow(unused_variables)]
    pub fn get(self, a: A) -> B
    where
        B: Sized, // TODO: don't require this (problem: return type needs to be sized)
    {
        dead
    }

    /// Returns a new mapping, where `a` is now mapped to `b`.
    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Map.set"]
    #[allow(unused_variables)]
    pub fn set(self, a: A, b: B) -> Self {
        dead
    }

    /// Create a mapping, where every value of type `a` is mapped to `b`.
    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Const.const"]
    #[allow(unused_variables)]
    pub fn cst(b: B) -> Self {
        dead
    }
}

impl<A: ?Sized, B> IndexLogic<A> for Mapping<A, B> {
    type Item = B;

    #[logic]
    #[open]
    fn index_logic(self, a: A) -> B {
        self.get(a)
    }
}
