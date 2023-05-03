use crate::*;

#[cfg_attr(creusot, creusot::builtins = "set.Fset.fset")]
pub struct FSet<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> FSet<T> {
    #[cfg(creusot)]
    #[trusted]
    #[creusot::builtins = "set.Fset.empty"]
    pub const EMPTY: Self = { FSet(std::marker::PhantomData) };

    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn contains(self, e: T) -> bool {
        Self::mem(e, self)
    }

    #[logic]
    #[creusot::builtins = "set.Fset.mem"]
    fn mem(_: T, _: Self) -> bool {
        pearlite! { absurd }
    }

    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn insert(self, e: T) -> Self {
        Self::add(e, self)
    }

    #[logic]
    #[creusot::builtins = "set.Fset.add"]
    fn add(_: T, _: Self) -> Self {
        pearlite! { absurd }
    }

    #[predicate]
    #[creusot::builtins = "set.Fset.is_empty"]
    pub fn is_empty(self) -> bool {
        pearlite! { absurd }
    }

    #[logic]
    #[why3::attr = "inline:trivial"]
    pub fn remove(self, a: T) -> Self {
        Self::rem(a, self)
    }

    #[logic]
    #[creusot::builtins = "set.Fset.remove"]
    pub fn rem(_: T, _: Self) -> Self {
        pearlite! { absurd }
    }

    #[logic]
    #[creusot::builtins = "set.Fset.union"]
    pub fn union(self, _: Self) -> Self {
        pearlite! { absurd }
    }

    #[predicate]
    #[creusot::builtins = "set.Fset.subset"]
    pub fn is_subset(self, _: Self) -> bool {
        pearlite! { absurd }
    }

    #[predicate]
    #[why3::attr = "inline:trivial"]
    pub fn is_superset(self, other: Self) -> bool {
        Self::is_subset(other, self)
    }

    #[logic]
    #[creusot::builtins = "set.Fset.cardinal"]
    pub fn len(self) -> Int {
        pearlite! { absurd }
    }

    #[logic]
    #[creusot::builtins = "set.Fset.pick"]
    pub fn peek(self) -> T
    where
        T: Sized,
    {
        pearlite! { absurd }
    }

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
