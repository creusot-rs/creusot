#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{
    invariant::*,
    std::ops::{
        Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
    },
    *,
};
#[cfg(feature = "nightly")]
use ::std::alloc::Allocator;
pub use ::std::slice::*;

impl<T> Invariant for [T] {
    #[logic(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { inv(self@) }
    }
}

impl<T> View for [T] {
    type ViewTy = Seq<T>;

    // We define this as trusted because builtins and ensures are incompatible
    #[logic]
    #[trusted]
    #[ensures(result.len() <= usize::MAX@)]
    #[ensures(result == slice_model(&self))]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T: DeepModel> DeepModel for [T] {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[ensures((&self)@.len() == result.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == (&self)[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

#[logic]
#[trusted]
#[cfg_attr(target_pointer_width = "16", creusot::builtins = "creusot.slice.Slice16.id")]
#[cfg_attr(target_pointer_width = "32", creusot::builtins = "creusot.slice.Slice32.id")]
#[cfg_attr(target_pointer_width = "64", creusot::builtins = "creusot.slice.Slice64.id")]
pub fn slice_model<T>(_: &[T]) -> Seq<T> {
    dead
}

#[logic]
#[open]
pub fn slice_len<T>(x: [T]) -> Int {
    pearlite! { x@.len() }
}

pub trait SliceExt<T> {
    #[logic]
    fn to_mut_seq(&mut self) -> Seq<&mut T>;

    #[logic]
    fn to_ref_seq(&self) -> Seq<&T>;
}

impl<T> SliceExt<T> for [T] {
    #[logic]
    #[trusted]
    #[ensures(result.len() == self@.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == &mut self[i])]
    // TODO: replace with a map function applied on a sequence
    fn to_mut_seq(&mut self) -> Seq<&mut T> {
        dead
    }

    #[logic]
    #[trusted]
    #[ensures(result.len() == self@.len())]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> result[i] == &self[i])]
    fn to_ref_seq(&self) -> Seq<&T> {
        dead
    }
}

pub trait SliceIndex<T: ?Sized>: ::std::slice::SliceIndex<T>
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

impl<T> SliceIndex<[T]> for usize {
    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self@ < seq.len() }
    }

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn has_value(self, seq: Seq<T>, out: T) -> bool {
        pearlite! { seq[self@] == out }
    }

    #[logic]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i> 0 <= i && i != self@ && i < old.len() ==> old[i] == fin[i] }
    }
}

impl<T> SliceIndex<[T]> for Range<usize> {
    #[logic]
    #[open]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.start@ <= self.end@ && self.end@ <= seq.len() }
    }

    #[logic]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(self.start@, self.end@) == out@ }
    }

    #[logic]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i> 0 <= i && (i < self.start@ || self.end@ <= i) && i < old.len()
            ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndex<[T]> for RangeInclusive<usize> {
    #[logic]
    #[trusted]
    #[ensures(self.end_log()@ < seq.len() && self.start_log()@ <= self.end_log()@+1 ==> result)]
    #[ensures(self.end_log()@ >= seq.len() ==> !result)]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        dead
    }

    #[logic]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! {
            if self.is_empty_log() { out@ == Seq::empty() }
            else { seq.subsequence(self.start_log()@, self.end_log()@ + 1) == out@ }
        }
    }

    #[logic]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i> 0 <= i
                && (i < self.start_log()@ || self.end_log()@ < i || self.is_empty_log())
                && i < old.len()
                ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndex<[T]> for RangeTo<usize> {
    #[logic]
    #[open]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.end@ <= seq.len() }
    }

    #[logic]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(0, self.end@) == out@ }
    }

    #[logic]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i> self.end@ <= i && i < old.len() ==> old[i] == fin[i] }
    }
}

impl<T> SliceIndex<[T]> for RangeFrom<usize> {
    #[logic]
    #[open]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.start@ <= seq.len() }
    }

    #[logic]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(self.start@, seq.len()) == out@ }
    }

    #[logic]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i> 0 <= i && i < self.start@ && i < old.len() ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndex<[T]> for RangeFull {
    #[logic]
    #[open]
    fn in_bounds(self, _seq: Seq<T>) -> bool {
        pearlite! { true }
    }

    #[logic]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq == out@ }
    }

    #[logic]
    #[open]
    fn resolve_elswhere(self, _old: Seq<T>, _fin: Seq<T>) -> bool {
        pearlite! { true }
    }
}

impl<T> SliceIndex<[T]> for RangeToInclusive<usize> {
    #[logic]
    #[open]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.end@ < seq.len() }
    }

    #[logic]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(0, self.end@ + 1) == out@ }
    }

    #[logic]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i> self.end@ < i && i < old.len() ==> old[i] == fin[i] }
    }
}

extern_spec! {
    impl<T> [T] {
        #[pure]
        #[requires(self@.len() == src@.len())]
        #[ensures((^self)@ == src@)]
        fn copy_from_slice(&mut self, src: &[T]) where T: Copy;

        #[pure]
        #[ensures(self@.len() == result@)]
        fn len(&self) -> usize;

        #[pure]
        #[requires(i@ < self@.len())]
        #[requires(j@ < self@.len())]
        #[ensures((^self)@.exchange(self@, i@, j@))]
        fn swap(&mut self, i: usize, j: usize);

        #[ensures(ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, *r))]
        #[ensures(ix.in_bounds(self@) || result == None)]
        fn get<I: SliceIndex<[T]>>(&self, ix: I) -> Option<&<I as ::std::slice::SliceIndex<[T]>>::Output>;

        #[ensures((^self)@.len() == self@.len())]
        #[ensures(ix.in_bounds(self@) ==> exists<r> result == Some(r) && ix.has_value(self@, *r) && ix.has_value((^self)@, ^r) && ix.resolve_elswhere(self@, (^self)@))]
        #[ensures(ix.in_bounds(self@) || result == None)]
        fn get_mut<I: SliceIndex<[T]>>(&mut self, ix: I) -> Option<&mut <I as ::std::slice::SliceIndex<[T]>>::Output>;

        #[pure]
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

        #[pure]
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

        #[pure]
        #[ensures(match result {
            Some(r) => {
                *r == (**self)[0] && ^r == (^*self)[0] &&
                (**self)@.len() > 0 && (^*self)@.len() > 0 &&
                (*^self)@ == (**self)@.tail() && (^^self)@ == (^*self)@.tail()
            }
            None => (*^self)@ == Seq::empty() && (^*self)@ == Seq::empty() &&
                    (**self)@ == Seq::empty() && (^^self)@ == Seq::empty()
        })]
        fn take_first_mut<'a>(self_: &mut &'a mut [T]) -> Option<&'a mut T>;

        #[pure]
        #[ensures(result@ == self)]
        fn iter(&self) -> Iter<'_, T>;

        #[pure]
        #[ensures(result@ == self)]
        fn iter_mut(&mut self) -> IterMut<'_, T>;

        #[pure]
        #[ensures(result == None ==> self@.len() == 0)]
        #[ensures(forall<x> result == Some(x) ==> self[self@.len() - 1] == *x)]
        fn last(&self) -> Option<&T>;

        #[pure]
        #[ensures(result == None ==> self@.len() == 0)]
        #[ensures(forall<x> result == Some(x) ==> self[0] == *x)]
        fn first(&self) -> Option<&T>;


        #[requires(self.deep_model().sorted())]
        #[ensures(forall<i:usize> result == Ok(i) ==> i@ < self@.len() && (*self).deep_model()[i@] == x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==> i@ <= self@.len() &&
            forall<j> 0 <= j && j < self@.len() ==> self.deep_model()[j] != x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==>
            forall<j:usize> j < i ==> self.deep_model()[j@] < x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==>
            forall<j:usize> i <= j && j@ < self@.len() ==> x.deep_model() < self.deep_model()[j@])]
        fn binary_search(&self, x: &T) -> Result<usize, usize>
            where T: Ord + DeepModel,  T::DeepModelTy: OrdLogic,;

        #[terminates] // can OOM (?)
        #[ensures(result@ == self_@)]
        fn into_vec<A: Allocator>(self_: Box<Self, A>) -> Vec<T, A>;

        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        unsafe fn get_unchecked<I>(&self, ix: I) -> &<I as ::std::slice::SliceIndex<[T]>>::Output
            where I: SliceIndex<[T]>;

        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        #[ensures(ix.has_value((^self)@, ^result))]
        #[ensures(ix.resolve_elswhere(self@, (^self)@))]
        #[ensures((^self)@.len() == self@.len())]
        unsafe fn get_unchecked_mut<I>(&mut self, ix: I) -> &mut <I as ::std::slice::SliceIndex<[T]>>::Output
            where I: SliceIndex<[T]>;
    }

    impl<T, I> IndexMut<I> for [T]
        where I: SliceIndex<[T]> {
        #[pure]
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        #[ensures(ix.has_value((&^self)@, ^result))]
        #[ensures(ix.resolve_elswhere(self@, (&^self)@))]
        #[ensures((&^self)@.len() == self@.len())]
        fn index_mut(&mut self, ix: I) -> &mut <[T] as Index<I>>::Output;
    }

    impl<T, I> Index<I> for [T]
        where I: SliceIndex<[T]> {
        #[pure]
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        fn index(&self, ix: I) -> &<[T] as Index<I>>::Output;
    }

    impl<'a, T> IntoIterator for &'a [T] {
        #[ensures(self == result@)]
        fn into_iter(self) -> Iter<'a, T>;
    }

    impl<'a, T> IntoIterator for &'a mut [T] {
        #[ensures(self == result@)]
        fn into_iter(self) -> IterMut<'a, T>;
    }

    impl<'a, T> Default for &'a mut [T] {
        #[ensures((*result)@ == Seq::empty())]
        #[ensures((^result)@ == Seq::empty())]
        fn default() -> &'a mut [T];
    }

    impl<'a, T> Default for &'a [T] {
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
            #[pure]
            #[ensures(result@.len() == 1)]
            #[ensures(result@[0] == *s)]
            fn from_ref<T>(s: &T) -> &[T];

            #[pure]
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

    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    #[logic(prophetic)]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && (*self@)@ == Seq::empty() }
    }

    #[logic]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            self@.to_ref_seq() == visited.concat(tl@.to_ref_seq())
        }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> View for IterMut<'a, T> {
    type ViewTy = &'a mut [T];

    #[logic]
    #[trusted]
    #[ensures((^result)@.len() == (*result)@.len())]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T> Resolve for IterMut<'a, T> {
    #[open]
    #[logic(prophetic)]
    fn resolve(self) -> bool {
        pearlite! { *self@ == ^self@ }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<'a, T> Iterator for IterMut<'a, T> {
    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && (*self@)@ == Seq::empty() }
    }

    #[logic]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            self@.to_mut_seq() == visited.concat(tl@.to_mut_seq())
        }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
