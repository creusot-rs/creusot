#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{ghost::perm::Perm, invariant::*, logic::ops::IndexLogic, prelude::*};
#[cfg(feature = "nightly")]
use std::alloc::Allocator;
use std::{
    ops::{
        Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
    },
    slice::*,
};

impl<T> Invariant for [T] {
    #[logic(open, prophetic)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { inv(self@) }
    }
}

impl<T> Resolve for [T] {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn resolve(self) -> bool {
        pearlite! { forall<i> 0 <= i && i < self@.len() ==> resolve(self[i]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<T> View for [T] {
    type ViewTy = Seq<T>;

    #[logic]
    #[cfg_attr(target_pointer_width = "16", builtin("creusot.slice.Slice16.view"))]
    #[cfg_attr(target_pointer_width = "32", builtin("creusot.slice.Slice32.view"))]
    #[cfg_attr(target_pointer_width = "64", builtin("creusot.slice.Slice64.view"))]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T: DeepModel> DeepModel for [T] {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[trusted]
    #[logic(opaque)]
    #[ensures((&self)@.len() == result.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == (&self)[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl<T> IndexLogic<Int> for [T] {
    type Item = T;

    #[logic(open, inline)]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T> IndexLogic<usize> for [T] {
    type Item = T;

    #[logic(open, inline)]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

pub trait SliceExt<T> {
    #[logic]
    fn to_mut_seq(&mut self) -> Seq<&mut T>;

    #[logic]
    fn to_ref_seq(&self) -> Seq<&T>;

    #[check(terminates)]
    fn as_ptr_perm(&self) -> (*const T, Ghost<&Perm<*const [T]>>);

    #[check(terminates)]
    fn as_mut_ptr_perm(&mut self) -> (*mut T, Ghost<&mut Perm<*const [T]>>);
}

impl<T> SliceExt<T> for [T] {
    #[trusted]
    #[logic(opaque)]
    #[ensures(result.len() == self@.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == &mut self[i])]
    // TODO: replace with a map function applied on a sequence
    fn to_mut_seq(&mut self) -> Seq<&mut T> {
        dead
    }

    #[trusted]
    #[logic(opaque)]
    #[ensures(result.len() == self@.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == &self[i])]
    fn to_ref_seq(&self) -> Seq<&T> {
        dead
    }

    /// Convert `&[T]` to `*const T` and a shared ownership token.
    #[check(terminates)]
    #[ensures(result.0 == *result.1.ward() as *const T)]
    #[ensures(self == result.1.val())]
    #[erasure(Self::as_ptr)]
    fn as_ptr_perm(&self) -> (*const T, Ghost<&Perm<*const [T]>>) {
        let (ptr, own) = Perm::from_ref(self);
        (ptr as *const T, own)
    }

    /// Convert `&mut [T]` to `*mut T` and a mutable ownership token.
    #[check(terminates)]
    #[ensures(result.0 as *const T == *result.1.ward() as *const T)]
    #[ensures(&*self == result.1.val())]
    #[ensures(&^self == (^result.1).val())]
    #[erasure(Self::as_mut_ptr)]
    fn as_mut_ptr_perm(&mut self) -> (*mut T, Ghost<&mut Perm<*const [T]>>) {
        let (ptr, own) = Perm::from_mut(self);
        (ptr as *mut T, own)
    }
}

pub trait SliceIndexSpec<T: ?Sized>: SliceIndex<T>
where
    T: View,
{
    #[logic]
    fn in_bounds(self, seq: T::ViewTy) -> bool;

    #[logic]
    fn has_value(self, seq: T::ViewTy, out: Self::Output) -> bool;

    #[logic]
    fn resolve_elswhere(self, old: T::ViewTy, fin: T::ViewTy) -> bool;
}

impl<T> SliceIndexSpec<[T]> for usize {
    #[logic(open, inline)]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self@ < seq.len() }
    }

    #[logic(open, inline)]
    fn has_value(self, seq: Seq<T>, out: T) -> bool {
        pearlite! { seq[self@] == out }
    }

    #[logic(open, inline)]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i> 0 <= i && i != self@ && i < old.len() ==> old[i] == fin[i] }
    }
}

impl<T> SliceIndexSpec<[T]> for Range<usize> {
    #[logic(open)]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.start@ <= self.end@ && self.end@ <= seq.len() }
    }

    #[logic(open)]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(self.start@, self.end@) == out@ }
    }

    #[logic(open)]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i> 0 <= i && (i < self.start@ || self.end@ <= i) && i < old.len()
            ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeInclusive<usize> {
    #[trusted]
    #[logic(opaque)]
    #[ensures(self.end_log()@ < seq.len() && self.start_log()@ <= self.end_log()@+1 ==> result)]
    #[ensures(self.end_log()@ >= seq.len() ==> !result)]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        dead
    }

    #[logic(open)]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! {
            if self.is_empty_log() { out@ == Seq::empty() }
            else { seq.subsequence(self.start_log()@, self.end_log()@ + 1) == out@ }
        }
    }

    #[logic(open)]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i> 0 <= i
                && (i < self.start_log()@ || self.end_log()@ < i || self.is_empty_log())
                && i < old.len()
                ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeTo<usize> {
    #[logic(open)]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.end@ <= seq.len() }
    }

    #[logic(open)]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(0, self.end@) == out@ }
    }

    #[logic(open)]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i> self.end@ <= i && i < old.len() ==> old[i] == fin[i] }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeFrom<usize> {
    #[logic(open)]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.start@ <= seq.len() }
    }

    #[logic(open)]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(self.start@, seq.len()) == out@ }
    }

    #[logic(open)]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i> 0 <= i && i < self.start@ && i < old.len() ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeFull {
    #[logic(open)]
    fn in_bounds(self, _seq: Seq<T>) -> bool {
        pearlite! { true }
    }

    #[logic(open)]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq == out@ }
    }

    #[logic(open)]
    fn resolve_elswhere(self, _old: Seq<T>, _fin: Seq<T>) -> bool {
        pearlite! { true }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeToInclusive<usize> {
    #[logic(open)]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.end@ < seq.len() }
    }

    #[logic(open)]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(0, self.end@ + 1) == out@ }
    }

    #[logic(open)]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i> self.end@ < i && i < old.len() ==> old[i] == fin[i] }
    }
}

extern_spec! {
    impl<T> [T] {
        #[check(ghost)]
        #[requires(self@.len() == src@.len())]
        #[ensures((^self)@ == src@)]
        fn copy_from_slice(&mut self, src: &[T]) where T: Copy;

        #[check(ghost)]
        #[ensures(self@.len() == result@)]
        fn len(&self) -> usize;

        #[check(ghost)]
        #[requires(i@ < self@.len())]
        #[requires(j@ < self@.len())]
        #[ensures((^self)@.exchange(self@, i@, j@))]
        fn swap(&mut self, i: usize, j: usize);

        #[ensures(ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, *r))]
        #[ensures(ix.in_bounds(self@) || result == None)]
        fn get<I: SliceIndexSpec<[T]>>(&self, ix: I) -> Option<&<I as SliceIndex<[T]>>::Output>;

        #[ensures((^self)@.len() == self@.len())]
        #[ensures(ix.in_bounds(self@) ==> exists<r>
                    result == Some(r) &&
                    ix.has_value(self@, *r) &&
                    ix.has_value((^self)@, ^r) &&
                    ix.resolve_elswhere(self@, (^self)@))]
        #[ensures(ix.in_bounds(self@) || result == None)]
        fn get_mut<I: SliceIndexSpec<[T]>>(&mut self, ix: I)
            -> Option<&mut <I as SliceIndex<[T]>>::Output>;

        #[check(ghost)]
        #[requires(mid@ <= self@.len())]
        #[ensures({
            let (l,r) = result;  let sl = self@.len();
            ((^self)@.len() == sl) &&
            self@.subsequence(0, mid@) == l@ &&
            self@.subsequence(mid@, sl) == r@ &&
            (^self)@.subsequence(0, mid@) == (^l)@ &&
            (^self)@.subsequence(mid@, sl) == (^r)@
        })]
        fn split_at_mut(&mut self, mid: usize) -> (&mut [T], &mut [T]);

        #[check(ghost)]
        #[ensures(match result {
            Some((first, tail)) => {
                *first == self[0] && ^first == (^self)[0] &&
                (*self)@.len() > 0 && (^self)@.len() > 0 &&
                (*tail)@ == (*self)@.tail() &&
                (^tail)@ == (^self)@.tail()
            }
            None => self@.len() == 0 && ^self == *self && self@ == Seq::empty()
        })]
        fn split_first_mut(&mut self) -> Option<(&mut T, &mut [T])>;

        #[check(ghost)]
        #[ensures(match result {
            Some(r) => {
                *r == (**self)[0] && ^r == (^*self)[0] &&
                (**self)@.len() > 0 && (^*self)@.len() > 0 &&
                (*^self)@ == (**self)@.tail() && (^^self)@ == (^*self)@.tail()
            }
            None => (*^self)@ == Seq::empty() && (^*self)@ == Seq::empty() &&
                    (**self)@ == Seq::empty() && (^^self)@ == Seq::empty()
        })]
        fn split_off_first_mut<'a>(self: &mut &'a mut [T]) -> Option<&'a mut T>;

        #[check(ghost)]
        #[ensures(result@ == self)]
        fn iter(&self) -> Iter<'_, T>;

        #[check(ghost)]
        #[ensures(result@ == self)]
        fn iter_mut(&mut self) -> IterMut<'_, T>;

        #[check(ghost)]
        #[ensures(result == None ==> self@.len() == 0)]
        #[ensures(forall<x> result == Some(x) ==> self[self@.len() - 1] == *x)]
        fn last(&self) -> Option<&T>;

        #[check(ghost)]
        #[ensures(result == None ==> self@.len() == 0)]
        #[ensures(forall<x> result == Some(x) ==> self[0] == *x)]
        fn first(&self) -> Option<&T>;


        #[requires(self.deep_model().sorted())]
        #[ensures(forall<i:usize> result == Ok(i) ==>
            i@ < self@.len() && (*self).deep_model()[i@] == x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==> i@ <= self@.len() &&
            forall<j> 0 <= j && j < self@.len() ==> self.deep_model()[j] != x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==>
            forall<j:usize> j < i ==> self.deep_model()[j@] < x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==>
            forall<j:usize> i <= j && j@ < self@.len() ==> x.deep_model() < self.deep_model()[j@])]
        fn binary_search(&self, x: &T) -> Result<usize, usize>
            where T: Ord + DeepModel,  T::DeepModelTy: OrdLogic,;

        #[check(terminates)] // can OOM (?)
        #[ensures(result@ == self_@)]
        fn into_vec<A: Allocator>(self_: Box<Self, A>) -> Vec<T, A>;

        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        unsafe fn get_unchecked<I: SliceIndexSpec<[T]>>(&self, ix: I)
            -> &<I as SliceIndex<[T]>>::Output;

        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        #[ensures(ix.has_value((^self)@, ^result))]
        #[ensures(ix.resolve_elswhere(self@, (^self)@))]
        #[ensures((^self)@.len() == self@.len())]
        unsafe fn get_unchecked_mut<I: SliceIndexSpec<[T]>>(&mut self, ix: I)
            -> &mut <I as SliceIndex<[T]>>::Output;

        // Calling this is safe but you should use `as_ptr_perm` instead to prove things.
        #[check(ghost)]
        fn as_ptr(&self) -> *const T;

        // Calling this is safe but you should use `as_mut_ptr_perm` instead to prove things.
        #[check(ghost)]
        fn as_mut_ptr(&mut self) -> *mut T;
    }

    impl<T, I: SliceIndexSpec<[T]>> IndexMut<I> for [T] {
        #[check(ghost)]
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        #[ensures(ix.has_value((&^self)@, ^result))]
        #[ensures(ix.resolve_elswhere(self@, (&^self)@))]
        #[ensures((&^self)@.len() == self@.len())]
        fn index_mut(&mut self, ix: I) -> &mut <[T] as Index<I>>::Output;
    }

    impl<T, I: SliceIndexSpec<[T]>> Index<I> for [T] {
        #[check(ghost)]
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        fn index(&self, ix: I) -> &<[T] as Index<I>>::Output;
    }

    impl<'a, T> IntoIterator for &'a [T] {
        #[check(ghost)]
        #[ensures(self == result@)]
        fn into_iter(self) -> Iter<'a, T>;
    }

    impl<'a, T> IntoIterator for &'a mut [T] {
        #[check(ghost)]
        #[ensures(self == result@)]
        fn into_iter(self) -> IterMut<'a, T>;
    }

    impl<'a, T> Default for &'a mut [T] {
        #[check(ghost)]
        #[ensures((*result)@ == Seq::empty())]
        #[ensures((^result)@ == Seq::empty())]
        fn default() -> &'a mut [T];
    }

    impl<'a, T> Default for &'a [T] {
        #[check(ghost)]
        #[ensures(result@ == Seq::empty())]
        fn default() -> &'a [T];
    }

    impl<T: Clone, A: Allocator + Clone> Clone for Box<[T], A> {
        #[ensures(forall<i> 0 <= i && i < self@.len() ==>
            T::clone.postcondition((&self@[i],), result@[i]))]
        fn clone(&self) -> Box<[T], A>;
    }

    mod std {
        mod slice {
            #[check(ghost)]
            #[ensures(result@.len() == 1)]
            #[ensures(result@[0] == *s)]
            fn from_ref<T>(s: &T) -> &[T];

            #[check(ghost)]
            #[ensures(result@.len() == 1)]
            #[ensures(result@[0] == *s)]
            #[ensures((^result)@.len() == 1)]
            #[ensures((^result)@[0] == ^s)]
            fn from_mut<T>(s: &mut T) -> &mut [T];
        }
    }
}

impl<'a, T> View for Iter<'a, T> {
    type ViewTy = &'a [T];

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T> IteratorSpec for Iter<'a, T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { resolve(self) && (*self@)@ == Seq::empty() }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            self@.to_ref_seq() == visited.concat(tl@.to_ref_seq())
        }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> View for IterMut<'a, T> {
    type ViewTy = &'a mut [T];

    #[trusted]
    #[logic(opaque)]
    #[ensures((^result)@.len() == (*result)@.len())]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T> Resolve for IterMut<'a, T> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        pearlite! { *self@ == ^self@ }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<'a, T> IteratorSpec for IterMut<'a, T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { resolve(self) && (*self@)@ == Seq::empty() }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            self@.to_mut_seq() == visited.concat(tl@.to_mut_seq())
        }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
