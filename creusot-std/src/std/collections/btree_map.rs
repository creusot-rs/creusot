#[cfg(feature = "nightly")]
use crate::logic::FMap;
#[cfg(creusot)]
use crate::{
    invariant::inv,
    resolve::structural_resolve,
    std::ops::{RangeBoundsSpec, between},
};
use crate::{
    prelude::*,
    std::iter::{DoubleEndedIteratorSpec, ExactSizeIteratorSpec, IteratorSpec},
};
#[cfg(creusot)]
use core::ops::Bound;
#[cfg(feature = "nightly")]
use std::alloc::Allocator;
use std::collections::btree_map::*;
#[cfg(creusot)]
use std::{borrow::Borrow, ops::Index, ops::RangeBounds};

#[cfg(feature = "nightly")]
impl<K: DeepModel, V, A: Allocator + Clone> View for BTreeMap<K, V, A> {
    type ViewTy = FMap<K::DeepModelTy, V>;

    #[trusted]
    #[logic(opaque)]
    #[ensures(result.len() <= usize::MAX@)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<K: DeepModel, V, A: Allocator + Clone> Resolve for BTreeMap<K, V, A> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn resolve(self) -> bool {
        pearlite! { forall<k: K::DeepModelTy> self@.contains(&k) ==> resolve(self@[k]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

#[cfg(feature = "nightly")]
impl<K: DeepModel, V, A: Allocator + Clone> Invariant for BTreeMap<K, V, A> {
    #[logic(open, prophetic)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { inv(self@) }
    }
}

/// The keys of the entries in `s` are strictly increasing.
#[logic(open)]
pub fn keys_increasing<K: DeepModel<DeepModelTy: OrdLogic>, V>(s: Seq<(K, V)>) -> bool {
    pearlite! {
        forall<i, j> 0 <= i && i < j && j < s.len() ==> s[i].0.deep_model() < s[j].0.deep_model()
    }
}

/// `s` is the sequence of the keys of `m`, in increasing order.
#[logic(open)]
pub fn sorted_keys<K: DeepModel<DeepModelTy: OrdLogic>, V>(
    m: FMap<K::DeepModelTy, V>,
    s: Seq<K>,
) -> bool {
    pearlite! {
        s.len() == m.len()
        && (forall<i, j> 0 <= i && i < j && j < s.len() ==> s[i].deep_model() < s[j].deep_model())
        && (forall<i> 0 <= i && i < s.len() ==> m.contains(&s[i].deep_model()))
        && (forall<k: K::DeepModelTy> m.contains(&k) ==> exists<i> 0 <= i && i < s.len() && s[i].deep_model() == k)
    }
}

/// `s` is the sequence of the entries of `m`, sorted by increasing keys.
#[logic(open)]
pub fn sorted_entries<K: DeepModel<DeepModelTy: OrdLogic>, V>(
    m: FMap<K::DeepModelTy, V>,
    s: Seq<(K, V)>,
) -> bool {
    pearlite! {
        s.len() == m.len()
        && keys_increasing(s)
        && (forall<i> 0 <= i && i < s.len() ==> m.lookup(s[i].0.deep_model()) == Some(s[i].1))
        && (forall<k: K::DeepModelTy> m.contains(&k) ==> exists<i> 0 <= i && i < s.len() && s[i].0.deep_model() == k)
    }
}

/// `s` is the sequence of (references to) the entries of `m`, sorted by increasing keys.
#[logic(open)]
pub fn sorted_entries_ref<K: DeepModel<DeepModelTy: OrdLogic>, V>(
    m: FMap<K::DeepModelTy, V>,
    s: Seq<(&K, &V)>,
) -> bool {
    pearlite! {
        s.len() == m.len()
        && keys_increasing(s)
        && (forall<i> 0 <= i && i < s.len() ==> m.lookup(s[i].0.deep_model()) == Some(*s[i].1))
        && (forall<k: K::DeepModelTy> m.contains(&k) ==> exists<i> 0 <= i && i < s.len() && s[i].0.deep_model() == k)
    }
}

/// `s` is the sequence of the entries of `cur`, sorted by increasing keys, with mutable
/// references to the values. `fin` is the map obtained after the end of these borrows.
#[logic(open, prophetic)]
pub fn sorted_entries_mut<K: DeepModel<DeepModelTy: OrdLogic>, V>(
    cur: FMap<K::DeepModelTy, V>,
    fin: FMap<K::DeepModelTy, V>,
    s: Seq<(&K, &mut V)>,
) -> bool {
    pearlite! {
        s.len() == cur.len()
        && keys_increasing(s)
        && (forall<i> 0 <= i && i < s.len() ==>
            cur.lookup(s[i].0.deep_model()) == Some(*s[i].1)
            && fin.lookup(s[i].0.deep_model()) == Some(^s[i].1))
        && (forall<k: K::DeepModelTy> cur.contains(&k) ==> exists<i> 0 <= i && i < s.len() && s[i].0.deep_model() == k)
        && (forall<k: K::DeepModelTy> fin.contains(&k) == cur.contains(&k))
    }
}

/// The bounds of a range for which [`BTreeMap::range`] does not panic.
#[logic(open)]
pub fn valid_range<T: OrdLogic>(lo: Bound<T>, hi: Bound<T>) -> bool {
    pearlite! {
        match (lo, hi) {
            (Bound::Excluded(lo), Bound::Excluded(hi)) => lo < hi,
            (Bound::Included(lo), Bound::Included(hi)) => lo <= hi,
            (Bound::Included(lo), Bound::Excluded(hi)) => lo <= hi,
            (Bound::Excluded(lo), Bound::Included(hi)) => lo <= hi,
            _ => true,
        }
    }
}

/// The restriction of `m` to the keys in the range `(lo, hi)`.
#[logic(open)]
pub fn restrict<K: OrdLogic, V>(m: FMap<K, V>, lo: Bound<K>, hi: Bound<K>) -> FMap<K, V> {
    m.filter(|(k, _v)| between(lo, k, hi))
}

extern_spec! {
    impl<K: DeepModel, V> BTreeMap<K, V> {
        #[check(ghost)]
        #[ensures(result@ == FMap::empty())]
        fn new() -> Self;
    }

    impl<K: DeepModel, V, A: Allocator + Clone> BTreeMap<K, V, A> {
        #[check(ghost)]
        #[ensures(result@ == self@.len())]
        fn len(&self) -> usize;

        #[check(ghost)]
        #[ensures(result == (self@.len() == 0))]
        fn is_empty(&self) -> bool;

        #[ensures((^self)@ == FMap::empty())]
        fn clear(&mut self);

        #[ensures(match result {
            Some(v) => self@.lookup(key.deep_model()) == Some(*v),
            None => !self@.contains(&key.deep_model()),
        })]
        fn get<'a, Q: ?Sized + Ord + DeepModel<DeepModelTy = K::DeepModelTy>>(&'a self, key: &Q) -> Option<&'a V>
        where
            K: Borrow<Q> + Ord;

        #[ensures(result == self@.contains(&key.deep_model()))]
        fn contains_key<Q: ?Sized + Ord + DeepModel<DeepModelTy = K::DeepModelTy>>(&self, key: &Q) -> bool
        where
            K: Borrow<Q> + Ord;

        #[ensures(match result {
            Some(v) => self@.lookup(key.deep_model()) == Some(*v)
                && (^self)@ == self@.add(key.deep_model(), ^v),
            None => !self@.contains(&key.deep_model()) && ^self == *self,
        })]
        fn get_mut<'a, Q: ?Sized + Ord + DeepModel<DeepModelTy = K::DeepModelTy>>(&'a mut self, key: &Q) -> Option<&'a mut V>
        where
            K: Borrow<Q> + Ord;

        #[ensures(result == self@.lookup(key.deep_model()))]
        #[ensures((^self)@ == self@.add(key.deep_model(), value))]
        fn insert(&mut self, key: K, value: V) -> Option<V>
        where
            K: Ord;

        #[ensures(result == self@.lookup(key.deep_model()))]
        #[ensures((^self)@ == self@.remove(key.deep_model()))]
        fn remove<Q: ?Sized + Ord + DeepModel<DeepModelTy = K::DeepModelTy>>(&mut self, key: &Q) -> Option<V>
        where
            K: Borrow<Q> + Ord;

    }

    impl<K: DeepModel<DeepModelTy: OrdLogic>, V, A: Allocator + Clone> BTreeMap<K, V, A> {
        #[check(ghost)]
        #[ensures(match result {
            Some((k, v)) => self@.lookup(k.deep_model()) == Some(*v)
                && forall<k2: K::DeepModelTy> self@.contains(&k2) ==> k.deep_model() <= k2,
            None => self@.len() == 0,
        })]
        fn first_key_value(&self) -> Option<(&K, &V)>
        where
            K: Ord;

        #[check(ghost)]
        #[ensures(match result {
            Some((k, v)) => self@.lookup(k.deep_model()) == Some(*v)
                && forall<k2: K::DeepModelTy> self@.contains(&k2) ==> k2 <= k.deep_model(),
            None => self@.len() == 0,
        })]
        fn last_key_value(&self) -> Option<(&K, &V)>
        where
            K: Ord;

        #[check(ghost)]
        #[ensures(match result {
            Some((k, v)) => self@.lookup(k.deep_model()) == Some(v)
                && (forall<k2: K::DeepModelTy> self@.contains(&k2) ==> k.deep_model() <= k2)
                && (^self)@ == self@.remove(k.deep_model()),
            None => self@.len() == 0 && ^self == *self,
        })]
        fn pop_first(&mut self) -> Option<(K, V)>
        where
            K: Ord;

        #[check(ghost)]
        #[ensures(match result {
            Some((k, v)) => self@.lookup(k.deep_model()) == Some(v)
                && (forall<k2: K::DeepModelTy> self@.contains(&k2) ==> k2 <= k.deep_model())
                && (^self)@ == self@.remove(k.deep_model()),
            None => self@.len() == 0 && ^self == *self,
        })]
        fn pop_last(&mut self) -> Option<(K, V)>
        where
            K: Ord;

        #[check(ghost)]
        #[ensures(sorted_entries_ref(self@, result@))]
        fn iter(&self) -> Iter<'_, K, V>;

        #[check(ghost)]
        #[ensures(sorted_entries_mut(self@, (^self)@, result@))]
        fn iter_mut(&mut self) -> IterMut<'_, K, V>;

        #[check(ghost)]
        #[ensures(sorted_keys(self@, result@))]
        fn keys(&self) -> Keys<'_, K, V>;

        #[check(ghost)]
        #[ensures(exists<s: Seq<(&K, &V)>> sorted_entries_ref(self@, s) && result@ == s.map(|(_k, v)| v))]
        fn values(&self) -> Values<'_, K, V>;

        #[check(ghost)]
        #[ensures(exists<s: Seq<(&K, &mut V)>> sorted_entries_mut(self@, (^self)@, s) && result@ == s.map(|(_k, v)| v))]
        fn values_mut(&mut self) -> ValuesMut<'_, K, V>;

        #[check(ghost)]
        #[ensures(sorted_keys(self@, result@))]
        fn into_keys(self) -> IntoKeys<K, V, A>;

        #[check(ghost)]
        #[ensures(exists<s: Seq<(K, V)>> sorted_entries(self@, s) && result@ == s.map(|(_k, v)| v))]
        fn into_values(self) -> IntoValues<K, V, A>;

        #[requires(valid_range(range.start_bound_logic().deep_model(), range.end_bound_logic().deep_model()))]
        #[ensures(sorted_entries_ref(
            restrict(self@, range.start_bound_logic().deep_model(), range.end_bound_logic().deep_model()),
            result@
        ))]
        fn range<T: ?Sized + Ord + DeepModel<DeepModelTy = K::DeepModelTy>, R: RangeBounds<T> + RangeBoundsSpec<T>>(&self, range: R) -> Range<'_, K, V>
        where
            K: Borrow<T> + Ord;

        #[requires(valid_range(range.start_bound_logic().deep_model(), range.end_bound_logic().deep_model()))]
        #[ensures(sorted_entries_mut(
            restrict(self@, range.start_bound_logic().deep_model(), range.end_bound_logic().deep_model()),
            restrict((^self)@, range.start_bound_logic().deep_model(), range.end_bound_logic().deep_model()),
            result@
        ))]
        #[ensures(forall<k: K::DeepModelTy>
            !between(range.start_bound_logic().deep_model(), k, range.end_bound_logic().deep_model())
            ==> (^self)@.lookup(k) == self@.lookup(k))]
        fn range_mut<T: ?Sized + Ord + DeepModel<DeepModelTy = K::DeepModelTy>, R: RangeBounds<T> + RangeBoundsSpec<T>>(&mut self, range: R) -> RangeMut<'_, K, V>
        where
            K: Borrow<T> + Ord;
    }

    impl<'q, K: DeepModel, Q: ?Sized + Ord + DeepModel<DeepModelTy = K::DeepModelTy>, V, A: Allocator + Clone> Index<&'q Q> for BTreeMap<K, V, A>
    where
        K: Borrow<Q> + Ord,
    {
        #[requires(self@.contains(&key.deep_model()))]
        #[ensures(*result == self@[key.deep_model()])]
        fn index<'a>(&'a self, key: &'q Q) -> &'a V;
    }

    impl<K: DeepModel, V> Default for BTreeMap<K, V> {
        #[check(ghost)]
        #[ensures(result@ == FMap::empty())]
        fn default() -> Self;
    }

    impl<K: DeepModel<DeepModelTy: OrdLogic>, V, A: Allocator + Clone> IntoIterator for BTreeMap<K, V, A> {
        #[check(ghost)]
        #[ensures(sorted_entries(self@, result@))]
        fn into_iter(self) -> IntoIter<K, V, A>;
    }

    impl<'a, K: DeepModel<DeepModelTy: OrdLogic>, V, A: Allocator + Clone> IntoIterator for &'a BTreeMap<K, V, A> {
        #[check(ghost)]
        #[ensures(sorted_entries_ref(self@, result@))]
        fn into_iter(self) -> Iter<'a, K, V>;
    }

    impl<'a, K: DeepModel<DeepModelTy: OrdLogic>, V, A: Allocator + Clone> IntoIterator for &'a mut BTreeMap<K, V, A> {
        #[check(ghost)]
        #[ensures(sorted_entries_mut((*self)@, (^self)@, result@))]
        fn into_iter(self) -> IterMut<'a, K, V>;
    }

    impl<K: Ord + DeepModel, V> FromIterator<(K, V)> for BTreeMap<K, V> {
        #[requires(T::into_iter.precondition((iter,)))]
        #[ensures(exists<into_iter: T::IntoIter, prod: Seq<(K, V)>, done: &mut T::IntoIter>
            T::into_iter.postcondition((iter,), into_iter) &&
            into_iter.produces(prod, *done) && done.completed() && resolve(^done) &&
            forall<k: K::DeepModelTy, v: V> (result@.lookup(k) == Some(v))
                == (exists<i, k1: K> 0 <= i && i < prod.len() && k1.deep_model() == k && prod[i] == (k1, v)
                    && forall<j> i < j && j < prod.len() ==> prod[j].0.deep_model() != k)
        )]
        fn from_iter<T: IntoIterator<Item = (K, V), IntoIter: IteratorSpec>>(iter: T) -> Self;
    }
}

/// Implements [`View`] and [`IteratorSpec`] for an iterator whose view is the sequence
/// of the items that it has yet to produce.
macro_rules! seq_iterator {
    ($(#[$attr:meta])* [$($gen:tt)*] $ty:ty, $item:ty) => {
        $(#[$attr])*
        impl $($gen)* View for $ty {
            type ViewTy = Seq<$item>;

            #[logic(opaque)]
            fn view(self) -> Self::ViewTy {
                dead
            }
        }

        $(#[$attr])*
        impl $($gen)* IteratorSpec for $ty {
            #[logic(open, prophetic)]
            fn completed(&mut self) -> bool {
                pearlite! { resolve(self) && self@ == Seq::empty() }
            }

            #[logic(open)]
            fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
                pearlite! { self@ == visited.concat(tl@) }
            }

            #[logic(law)]
            #[ensures(self.produces(Seq::empty(), self))]
            fn produces_refl(self) {
                let _ = Seq::<Self::Item>::concat_empty;
            }

            #[logic(law)]
            #[requires(a.produces(ab, b))]
            #[requires(b.produces(bc, c))]
            #[ensures(a.produces(ab.concat(bc), c))]
            fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
                let _ = Seq::<Self::Item>::concat_assoc;
            }
        }
    };
}

/// Implements [`DoubleEndedIteratorSpec`] and [`ExactSizeIteratorSpec`] for an iterator
/// implemented with [`seq_iterator`].
macro_rules! seq_iterator_exact_double_ended {
    ($(#[$attr:meta])* [$($gen:tt)*] $ty:ty) => {
        extern_spec! {
            impl $($gen)* Iterator for $ty {
                #[ensures(result.0@ == self@.len())]
                #[ensures(result.1 == Some(result.0))]
                fn size_hint(&self) -> (usize, Option<usize>);
            }
        }

        $(#[$attr])*
        impl $($gen)* ExactSizeIteratorSpec for $ty {
            #[logic(law)]
            #[requires(Self::size_hint.postcondition((self,), r))]
            #[ensures(r.1 == Some(r.0))]
            #[allow(unused_variables)]
            fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
        }

        $(#[$attr])*
        impl $($gen)* DoubleEndedIteratorSpec for $ty {
            #[logic(open)]
            fn produces_back(self, visited: Seq<Self::Item>, tl: Self) -> bool {
                pearlite! { self@ == tl@.concat(visited.reverse()) }
            }

            #[logic(open, prophetic)]
            fn completed_back(&mut self) -> bool {
                self.completed()
            }

            #[logic(law)]
            #[ensures(self.produces_back(Seq::empty(), self))]
            fn produces_back_refl(self) {
                let _ = Seq::<Self::Item>::reverse_empty();
                let _ = Seq::<Self::Item>::concat_empty;
            }

            #[logic(law)]
            #[requires(a.produces_back(ab, b))]
            #[requires(b.produces_back(bc, c))]
            #[ensures(a.produces_back(ab.concat(bc), c))]
            fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
                let _ = ab.reverse_concat(bc);
                let _ = Seq::<Self::Item>::concat_assoc;
            }

            #[logic(law)]
            #[requires(Self::size_hint.postcondition((self,), r))]
            #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
                self.produces_back(s, *i) && i.completed_back() ==> r.0@ <= s.len())]
            #[ensures(match r.1 {
                Some(r) => {
                    forall<s: Seq<Self::Item>, i: Self> self.produces_back(s, i) ==> s.len() <= r@
                }
                None => true
            })]
            fn size_hint_back_spec(&self, r: (usize, Option<usize>)) {}
        }
    };
}

/// Implements [`Resolve`] for an iterator implemented with [`seq_iterator`] whose items
/// contain a mutable borrow, accessed with the projection `$proj`: dropping the iterator
/// resolves the remaining borrows.
macro_rules! seq_iterator_resolve {
    ([$($gen:tt)*] $ty:ty, $($proj:tt)*) => {
        impl $($gen)* Resolve for $ty {
            #[logic(open, prophetic, inline)]
            fn resolve(self) -> bool {
                pearlite! { forall<i> 0 <= i && i < self@.len() ==> resolve(self@[i]$($proj)*) }
            }

            #[trusted]
            #[logic(prophetic)]
            #[requires(structural_resolve(self))]
            #[ensures(self.resolve())]
            fn resolve_coherence(self) {}
        }
    };
}

seq_iterator!([<'a, K, V>] Iter<'a, K, V>, (&'a K, &'a V));
seq_iterator_exact_double_ended!([<'a, K, V>] Iter<'a, K, V>);

seq_iterator!([<'a, K, V>] IterMut<'a, K, V>, (&'a K, &'a mut V));
seq_iterator_exact_double_ended!([<'a, K, V>] IterMut<'a, K, V>);
seq_iterator_resolve!([<'a, K, V>] IterMut<'a, K, V>, .1);

seq_iterator!([<'a, K, V>] Keys<'a, K, V>, &'a K);
seq_iterator_exact_double_ended!([<'a, K, V>] Keys<'a, K, V>);

seq_iterator!([<'a, K, V>] Values<'a, K, V>, &'a V);
seq_iterator_exact_double_ended!([<'a, K, V>] Values<'a, K, V>);

seq_iterator!([<'a, K, V>] ValuesMut<'a, K, V>, &'a mut V);
seq_iterator_exact_double_ended!([<'a, K, V>] ValuesMut<'a, K, V>);
seq_iterator_resolve!([<'a, K, V>] ValuesMut<'a, K, V>, );

// `Range` and `RangeMut` do not have a precise `size_hint`, so they do not implement
// `DoubleEndedIteratorSpec`.
seq_iterator!([<'a, K, V>] Range<'a, K, V>, (&'a K, &'a V));

seq_iterator!([<'a, K, V>] RangeMut<'a, K, V>, (&'a K, &'a mut V));
seq_iterator_resolve!([<'a, K, V>] RangeMut<'a, K, V>, .1);

seq_iterator!(#[cfg(feature = "nightly")] [<K, V, A: Allocator + Clone>] IntoIter<K, V, A>, (K, V));
seq_iterator_exact_double_ended!(#[cfg(feature = "nightly")] [<K, V, A: Allocator + Clone>] IntoIter<K, V, A>);

seq_iterator!(#[cfg(feature = "nightly")] [<K, V, A: Allocator + Clone>] IntoKeys<K, V, A>, K);
seq_iterator_exact_double_ended!(#[cfg(feature = "nightly")] [<K, V, A: Allocator + Clone>] IntoKeys<K, V, A>);

seq_iterator!(#[cfg(feature = "nightly")] [<K, V, A: Allocator + Clone>] IntoValues<K, V, A>, V);
seq_iterator_exact_double_ended!(#[cfg(feature = "nightly")] [<K, V, A: Allocator + Clone>] IntoValues<K, V, A>);

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
mod impls {
    use crate::{
        logic::FMap,
        prelude::*,
        std::iter::{DoubleEndedIteratorSpec, ExactSizeIteratorSpec},
    };
    use std::collections::btree_map::{BTreeMap, IntoIter, IntoKeys, IntoValues};

    impl<K: DeepModel, V> View for BTreeMap<K, V> {
        type ViewTy = FMap<K::DeepModelTy, V>;
    }
    impl<K: DeepModel, V> Resolve for BTreeMap<K, V> {}
    impl<K: DeepModel, V> Invariant for BTreeMap<K, V> {}

    impl<K, V> View for IntoIter<K, V> {
        type ViewTy = Seq<(K, V)>;
    }
    impl<K, V> IteratorSpec for IntoIter<K, V> {}
    impl<K, V> ExactSizeIteratorSpec for IntoIter<K, V> {}
    impl<K, V> DoubleEndedIteratorSpec for IntoIter<K, V> {}

    impl<K, V> View for IntoKeys<K, V> {
        type ViewTy = Seq<K>;
    }
    impl<K, V> IteratorSpec for IntoKeys<K, V> {}
    impl<K, V> ExactSizeIteratorSpec for IntoKeys<K, V> {}
    impl<K, V> DoubleEndedIteratorSpec for IntoKeys<K, V> {}

    impl<K, V> View for IntoValues<K, V> {
        type ViewTy = Seq<V>;
    }
    impl<K, V> IteratorSpec for IntoValues<K, V> {}
    impl<K, V> ExactSizeIteratorSpec for IntoValues<K, V> {}
    impl<K, V> DoubleEndedIteratorSpec for IntoValues<K, V> {}
}
