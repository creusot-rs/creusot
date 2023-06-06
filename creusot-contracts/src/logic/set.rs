use crate::*;

#[cfg_attr(creusot, creusot::builtins = "set.Set.set")]
pub struct Set<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> Set<T> {
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "set.Set.empty"]
    pub const EMPTY: Self = { Set(std::marker::PhantomData) };

    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn contains(self, e: T) -> bool {
        Self::mem(e, self)
    }

    #[doc(hidden)]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Set.mem"]
    pub fn mem(_: T, _: Self) -> bool {
        pearlite! { absurd }
    }

    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn insert(self, e: T) -> Self {
        Self::add(e, self)
    }

    #[doc(hidden)]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Set.add"]
    pub fn add(_: T, _: Self) -> Self {
        pearlite! { absurd }
    }

    #[open(self)]
    #[predicate]
    #[creusot::builtins = "set.Set.is_empty"]
    pub fn is_empty(self) -> bool {
        pearlite! { absurd }
    }

    #[open]
    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn remove(self, a: T) -> Self {
        Self::rem(a, self)
    }

    #[doc(hidden)]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Set.remove"]
    pub fn rem(_: T, _: Self) -> Self {
        pearlite! { absurd}
    }

    #[open(self)]
    #[logic]
    #[creusot::builtins = "set.Set.union"]
    pub fn union(self, _: Self) -> Self {
        pearlite! { absurd}
    }
}
