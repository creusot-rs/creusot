use crate::*;

#[trusted]
#[cfg_attr(creusot, creusot::builtins = "set.Fset.fset")]
pub struct FSet<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> FSet<T> {
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "set.Fset.empty"]
    pub const EMPTY: Self = { FSet(std::marker::PhantomData) };

    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn contains(self, e: T) -> bool {
        Self::mem(e, self)
    }

    #[doc(hidden)]
    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Fset.mem"]
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
    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Fset.add"]
    pub fn add(_: T, _: Self) -> Self {
        pearlite! { absurd }
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "set.Fset.is_empty"]
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
    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Fset.remove"]
    pub fn rem(_: T, _: Self) -> Self {
        pearlite! { absurd }
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Fset.union"]
    pub fn union(self, _: Self) -> Self {
        pearlite! { absurd }
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    #[creusot::builtins = "set.Fset.subset"]
    pub fn is_subset(self, _: Self) -> bool {
        pearlite! { absurd }
    }

    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn is_superset(self, other: Self) -> bool {
        Self::is_subset(other, self)
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Fset.cardinal"]
    pub fn len(self) -> Int {
        pearlite! { absurd }
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "set.Fset.pick"]
    pub fn peek(self) -> T
    where
        T: Sized,
    {
        pearlite! { absurd }
    }

    #[open]
    #[predicate]
    #[ensures(result ==> self == other)]
    pub fn ext_eq(self, other: Self) -> bool
    where
        T: Sized,
    {
        pearlite! {
            forall <e: T> self.contains(e) == other.contains(e)
        }
    }
}
