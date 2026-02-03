use crate::{
    logic::FSet,
    prelude::*,
    std::iter::{FromIteratorSpec, IteratorSpec},
};
#[cfg(feature = "nightly")]
use std::alloc::Allocator;
#[cfg(creusot)]
use std::borrow::Borrow;
use std::{collections::hash_set::*, hash::*};

#[cfg(feature = "nightly")]
impl<T: DeepModel, S, A: Allocator> View for HashSet<T, S, A> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

extern_spec! {
    mod std {
        mod collections {
            mod hash_set {
                impl<T: DeepModel, S, A: Allocator> HashSet<T, S, A> {
                    #[ensures(self@ == result@)]
                    fn iter(&self) -> Iter<'_, T>;
                }
                impl<T, S, A: Allocator> HashSet<T, S, A>
                where
                    T: Eq + Hash + DeepModel,
                    S: BuildHasher,
                {
                    #[ensures(result@ == self@.intersection(other@))]
                    fn intersection<'a>(&'a self, other: &'a HashSet<T, S, A>) -> Intersection<'a, T, S, A>;

                    #[ensures(result@ == self@.difference(other@))]
                    fn difference<'a>(&'a self, other: &'a HashSet<T, S, A>) -> Difference<'a, T, S, A>;

                    #[ensures(result == self@.contains(value.deep_model()))]
                    fn contains<Q: ?Sized>(&self, value: &Q) -> bool
                    where
                        T: Borrow<Q>,
                        Q: Eq + Hash + DeepModel<DeepModelTy = T::DeepModelTy>;
                }
            }
        }
    }

    impl<T: DeepModel, S, A: Allocator> IntoIterator for HashSet<T, S, A> {
        #[ensures(self@ == result@)]
        fn into_iter(self) -> IntoIter<T, A>;
    }

    impl<'a, T: DeepModel, S, A: Allocator> IntoIterator for &'a HashSet<T, S, A> {
        #[ensures(self@ == result@)]
        fn into_iter(self) -> Iter<'a, T>;
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel, A: Allocator> View for IntoIter<T, A> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[logic(open)]
pub fn set_produces<T: DeepModel, I: View<ViewTy = FSet<T::DeepModelTy>>>(
    start: I,
    visited: Seq<T>,
    end: I,
) -> bool {
    pearlite! { start@.len() == visited.len() + end@.len()
        && (forall<x: T::DeepModelTy> start@.contains(x) ==> (exists<x1: T> x1.deep_model() == x && visited.contains(x1)) || end@.contains(x))
        && (forall<x: T> visited.contains(x) ==> start@.contains(x.deep_model()) && !end@.contains(x.deep_model()))
        && (forall<x: T::DeepModelTy> end@.contains(x) ==> start@.contains(x) && !exists<x1: T> x1.deep_model() == x && visited.contains(x1))
        && (forall<i, j>
            0 <= i && i < visited.len() && 0 <= j && j < visited.len()
            && visited[i].deep_model() == visited[j].deep_model()
            ==> i == j)
    }
}

#[logic(open)]
#[requires(set_produces(a, ab, b))]
#[requires(set_produces(b, bc, c))]
#[ensures(set_produces(a, ab.concat(bc), c))]
pub fn set_produces_trans<T: DeepModel, I: View<ViewTy = FSet<T::DeepModelTy>>>(
    a: I,
    ab: Seq<T>,
    b: I,
    bc: Seq<T>,
    c: I,
) {
    Seq::<T>::concat_contains();
    proof_assert! { forall<i, x: T> ab.len() <= i && ab.concat(bc).get(i) == Some(x) ==> bc.contains(x) };
    proof_assert! { forall<i> 0 <= i && i < bc.len() ==> bc[i] == ab.concat(bc)[ab.len() + i] };
}

impl<T: DeepModel> IteratorSpec for IntoIter<T> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        set_produces(self, visited, o)
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (self@).is_empty() }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        set_produces_trans(a, ab, b, bc, c);
    }
}

impl<'a, T: DeepModel> View for Iter<'a, T> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T: DeepModel> IteratorSpec for Iter<'a, T> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        set_produces(self, visited, o)
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (self@).is_empty() }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        set_produces_trans(a, ab, b, bc, c);
    }
}

impl<T: Eq + Hash + DeepModel, S: Default + BuildHasher> FromIteratorSpec<T> for HashSet<T, S> {
    #[logic(open)]
    fn from_iter_post(prod: Seq<T>, res: Self) -> bool {
        pearlite! { forall<x: T::DeepModelTy> res@.contains(x) == exists<x1: T> x1.deep_model() == x && prod.contains(x1) }
    }
}

#[cfg(feature = "nightly")]
impl<'a, T: DeepModel, S, A: Allocator> View for Intersection<'a, T, S, A> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<'a, T: DeepModel, S, A: Allocator> View for Difference<'a, T, S, A> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T: Eq + Hash + DeepModel, S: BuildHasher> IteratorSpec for Intersection<'a, T, S> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        set_produces(self, visited, o)
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { resolve(self) && (self@).is_empty() }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        set_produces_trans(a, ab, b, bc, c);
    }
}

impl<'a, T: Eq + Hash + DeepModel, S: BuildHasher> IteratorSpec for Difference<'a, T, S> {
    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        set_produces(self, visited, o)
    }

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { resolve(self) && (self@).is_empty() }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        set_produces_trans(a, ab, b, bc, c);
    }
}

#[cfg(not(feature = "nightly"))]
mod impls {
    use crate::{logic::FSet, prelude::*};
    use std::collections::hash_set::{Difference, HashSet, Intersection, IntoIter};

    impl<K: DeepModel, S> View for HashSet<K, S> {
        type ViewTy = FSet<K::DeepModelTy>;
    }
    impl<K: DeepModel> View for IntoIter<K> {
        type ViewTy = FSet<K::DeepModelTy>;
    }
    impl<'a, T: DeepModel, S> View for Intersection<'a, T, S> {
        type ViewTy = FSet<T::DeepModelTy>;
    }
    impl<'a, T: DeepModel, S> View for Difference<'a, T, S> {
        type ViewTy = FSet<T::DeepModelTy>;
    }
}
