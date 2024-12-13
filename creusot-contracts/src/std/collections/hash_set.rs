use crate::{
    logic::FSet,
    std::iter::{FromIterator, IntoIterator, Iterator},
    *,
};
use ::std::{borrow::Borrow, collections::hash_set::*, hash::*};

impl<T: DeepModel, S> View for HashSet<T, S> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[open]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

extern_spec! {
    mod std {
        mod collections {
            mod hash_set {
                impl<T: DeepModel, S> HashSet<T, S> {
                    #[ensures(self@ == result@)]
                    fn iter(&self) -> Iter<'_, T>;
                }
                impl<T, S> HashSet<T, S>
                where
                    T: Eq + Hash + DeepModel,
                    S: BuildHasher,
                {
                    #[ensures(result@ == self@.intersection(other@))]
                    fn intersection<'a>(&'a self, other: &'a HashSet<T,S>) -> Intersection<'a, T, S>;

                    #[ensures(result == self@.contains(value.deep_model()))]
                    fn contains<Q: ?Sized>(&self, value: &Q) -> bool
                    where
                        T: Borrow<Q>,
                        Q: Eq + Hash + DeepModel<DeepModelTy = T::DeepModelTy>;
                }
            }
        }
    }
}

impl<T: DeepModel> View for IntoIter<T> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[open]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[open]
#[predicate]
pub fn set_produces<T: DeepModel, I: View<ViewTy = FSet<T::DeepModelTy>>>(
    start: I,
    visited: Seq<T>,
    end: I,
) -> bool {
    pearlite! { start@.len() == visited.len() + end@.len()
        && (forall<x: T::DeepModelTy> start@.contains(x) ==> (exists<x1: T> x1.deep_model() == x && visited.contains(x1)) || end@.contains(x))
        && (forall<x: T> visited.contains(x) ==> start@.contains(x.deep_model()) && !end@.contains(x.deep_model()))
        && (forall<x: T::DeepModelTy> end@.contains(x) ==> start@.contains(x) && !exists<x1: T> x1.deep_model() == x && visited.contains(x1))
        && (forall<i: Int, j: Int>
            0 <= i && i < visited.len() && 0 <= j && j < visited.len()
            && visited[i].deep_model() == visited[j].deep_model()
            ==> i == j)
    }
}

#[open]
#[logic]
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
    proof_assert! { forall<i: Int, x: T> ab.len() <= i && ab.concat(bc).get(i) == Some(x) ==> bc.contains(x) };
    proof_assert! { forall<i: Int> 0 <= i && i < bc.len() ==> bc[i] == ab.concat(bc)[ab.len() + i] };
}

impl<T: DeepModel> Iterator for IntoIter<T> {
    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        set_produces(self, visited, o)
    }

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (self@).is_empty() }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        set_produces_trans(a, ab, b, bc, c);
    }
}

impl<'a, T: DeepModel> View for Iter<'a, T> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[open]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T: DeepModel> Iterator for Iter<'a, T> {
    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        set_produces(self, visited, o)
    }

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (self@).is_empty() }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        set_produces_trans(a, ab, b, bc, c);
    }
}

impl<T: DeepModel, S> IntoIterator for HashSet<T, S> {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self@ == res@ }
    }
}

impl<T: DeepModel, S> IntoIterator for &HashSet<T, S> {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self@ == res@ }
    }
}

impl<T: Eq + Hash + DeepModel, S: Default + BuildHasher> FromIterator<T> for HashSet<T, S> {
    #[predicate]
    #[open]
    fn from_iter_post(prod: Seq<T>, res: Self) -> bool {
        pearlite! { forall<x: T::DeepModelTy> res@.contains(x) == exists<x1: T> x1.deep_model() == x && prod.contains(x1) }
    }
}

impl<'a, T: DeepModel, S> View for Intersection<'a, T, S> {
    type ViewTy = FSet<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[open]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T: Eq + Hash + DeepModel, S: BuildHasher> Iterator for Intersection<'a, T, S> {
    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        set_produces(self, visited, o)
    }

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && (self@).is_empty() }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        set_produces_trans(a, ab, b, bc, c);
    }
}
