use crate::{
    invariant::*,
    resolve::structural_resolve,
    std::ops::{Index, IndexMut, Range, RangeFrom, RangeFull, RangeTo, RangeToInclusive},
    *,
};
#[cfg(feature = "nightly")]
use ::std::alloc::Allocator;
pub use ::std::slice::*;

impl<T> Invariant for [T] {
    #[predicate(prophetic)]
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
    #[ensures(forall<i: Int> 0 <= i && i < result.len() ==> result[i] == (&self)[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

#[logic]
#[trusted]
#[cfg_attr(target_pointer_width = "16", creusot::builtins = "creusot.slice.Slice16.id")]
#[cfg_attr(target_pointer_width = "32", creusot::builtins = "creusot.slice.Slice32.id")]
#[cfg_attr(target_pointer_width = "64", creusot::builtins = "creusot.slice.Slice64.id")]
fn slice_model<T>(_: &[T]) -> Seq<T> {
    dead
}

#[logic]
#[open]
pub fn slice_len<T>(x: [T]) -> Int {
    pearlite! { x@.len() }
}

impl<T> Default for &mut [T] {
    #[open]
    #[predicate(prophetic)]
    fn is_default(self) -> bool {
        pearlite! { self@ == Seq::EMPTY && (^self)@ == Seq::EMPTY }
    }
}

impl<T> Default for &[T] {
    #[open]
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self@ == Seq::EMPTY }
    }
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
    #[ensures(forall<i : _> 0 <= i && i < result.len() ==> result[i] == &mut self[i])]
    // TODO: replace with a map function applied on a sequence
    fn to_mut_seq(&mut self) -> Seq<&mut T> {
        dead
    }

    #[logic]
    #[trusted]
    #[ensures(result.len() == self@.len())]
    #[ensures(forall<i : _> 0 <= i && i < result.len() ==> result[i] == &self[i])]
    fn to_ref_seq(&self) -> Seq<&T> {
        dead
    }
}

pub trait SliceIndex<T: ?Sized>: ::std::slice::SliceIndex<T>
where
    T: View,
{
    #[predicate]
    fn in_bounds(self, seq: T::ViewTy) -> bool;

    #[predicate]
    fn has_value(self, seq: T::ViewTy, out: Self::Output) -> bool;

    #[predicate]
    fn resolve_elswhere(self, old: T::ViewTy, fin: T::ViewTy) -> bool;
}

impl<T> SliceIndex<[T]> for usize {
    #[predicate]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self@ < seq.len() }
    }

    #[predicate]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn has_value(self, seq: Seq<T>, out: T) -> bool {
        pearlite! { seq[self@] == out }
    }

    #[predicate]
    #[open]
    #[creusot::why3_attr = "inline:trivial"]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i : Int> 0 <= i && i != self@ && i < old.len() ==> old[i] == fin[i] }
    }
}

impl<T> SliceIndex<[T]> for Range<usize> {
    #[predicate]
    #[open]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.start@ <= self.end@ && self.end@ <= seq.len() }
    }

    #[predicate]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(self.start@, self.end@) == out@ }
    }

    #[predicate]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i : Int> 0 <= i && (i < self.start@ || self.end@ <= i) && i < old.len()
            ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndex<[T]> for RangeTo<usize> {
    #[predicate]
    #[open]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.end@ <= seq.len() }
    }

    #[predicate]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(0, self.end@) == out@ }
    }

    #[predicate]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i : Int> self.end@ <= i && i < old.len() ==> old[i] == fin[i] }
    }
}

impl<T> SliceIndex<[T]> for RangeFrom<usize> {
    #[predicate]
    #[open]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.start@ <= seq.len() }
    }

    #[predicate]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(self.start@, seq.len()) == out@ }
    }

    #[predicate]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i : Int> 0 <= i && i < self.start@ && i < old.len() ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndex<[T]> for RangeFull {
    #[predicate]
    #[open]
    fn in_bounds(self, _seq: Seq<T>) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq == out@ }
    }

    #[predicate]
    #[open]
    fn resolve_elswhere(self, _old: Seq<T>, _fin: Seq<T>) -> bool {
        pearlite! { true }
    }
}

impl<T> SliceIndex<[T]> for RangeToInclusive<usize> {
    #[predicate]
    #[open]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { self.end@ < seq.len() }
    }

    #[predicate]
    #[open]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(0, self.end@ + 1) == out@ }
    }

    #[predicate]
    #[open]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i : Int> self.end@ < i && i < old.len() ==> old[i] == fin[i] }
    }
}

extern_spec! {
    impl<T> [T] {
        #[pure]
        #[requires(self@.len() == src@.len())]
        #[ensures((^self)@ == src@)]
        fn copy_from_slice(&mut self, src: &[T]) where T : Copy;

        #[pure]
        #[ensures(self@.len() == result@)]
        fn len(&self) -> usize;

        #[pure]
        #[requires(i@ < self@.len())]
        #[requires(j@ < self@.len())]
        #[ensures((^self)@.exchange(self@, i@, j@))]
        fn swap(&mut self, i: usize, j: usize);

        #[ensures(ix.in_bounds(self@) ==> exists<r: _> result == Some(r) && ix.has_value(self_@, *r))]
        #[ensures(ix.in_bounds(self@) || result == None)]
        fn get<I : SliceIndex<[T]>>(&self, ix: I) -> Option<&<I as ::std::slice::SliceIndex<[T]>>::Output>;

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
            None => self@.len() == 0 && ^self == *self && self@ == Seq::EMPTY
        })]
        fn split_first_mut(&mut self) -> Option<(&mut T, &mut [T])>;

        #[pure]
        #[ensures(match result {
            Some(r) => {
                *r == (**self)[0] && ^r == (^*self)[0] &&
                (**self)@.len() > 0 && (^*self)@.len() > 0 &&
                (*^self)@ == (**self)@.tail() && (^^self)@ == (^*self)@.tail()
            }
            None => (*^self)@ == Seq::EMPTY && (^*self)@ == Seq::EMPTY && (**self)@ == Seq::EMPTY && (^^self)@ == Seq::EMPTY
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
        #[ensures(forall<x : _> result == Some(x) ==> self[self@.len() - 1] == *x)]
        fn last(&self) -> Option<&T>;

        #[pure]
        #[ensures(result == None ==> self@.len() == 0)]
        #[ensures(forall<x : _> result == Some(x) ==> self[0] == *x)]
        fn first(&self) -> Option<&T>;


        #[requires(self.deep_model().sorted())]
        #[ensures(forall<i:usize> result == Ok(i) ==> i@ < self@.len() && (*self).deep_model()[i@] == x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==> i@ <= self@.len() &&
            forall<j : _> 0 <= j && j < self@.len() ==> self.deep_model()[j] != x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==>
            forall<j:usize> j < i ==> self.deep_model()[j@] < x.deep_model())]
        #[ensures(forall<i:usize> result == Err(i) ==>
            forall<j:usize> i <= j && j@ < self@.len() ==> x.deep_model() < self.deep_model()[j@])]
        fn binary_search(&self, x : &T) -> Result<usize, usize>
            where T: Ord + DeepModel,  T::DeepModelTy: OrdLogic,;

        #[terminates] // can OOM (?)
        #[ensures(result@ == self_@)]
        fn into_vec<A: Allocator>(self_: Box<Self, A>) -> Vec<T, A>;
    }

    impl<T, I> IndexMut<I> for [T]
        where I : SliceIndex<[T]> {
        #[pure]
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        #[ensures(ix.has_value((^self)@, ^result))]
        #[ensures(ix.resolve_elswhere(self@, (^self)@))]
        #[ensures((^self)@.len() == self@.len())]
        fn index_mut(&mut self, ix: I) -> &mut <[T] as Index<I>>::Output;
    }

    impl<T, I> Index<I> for [T]
        where I : SliceIndex<[T]> {
        #[pure]
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        fn index(&self, ix: I) -> &<[T] as Index<I>>::Output;
    }
}

impl<T> IntoIterator for &[T] {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self == res@ }
    }
}

impl<T> IntoIterator for &mut [T] {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self == res@ }
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
    #[predicate(prophetic)]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && (*self@)@ == Seq::EMPTY }
    }

    #[predicate]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            self@.to_ref_seq() == visited.concat(tl@.to_ref_seq())
        }
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
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! { *self@ == ^self@ }
    }

    #[trusted]
    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<'a, T> Iterator for IterMut<'a, T> {
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && (*self@)@ == Seq::EMPTY }
    }

    #[predicate]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            self@.to_mut_seq() == visited.concat(tl@.to_mut_seq())
        }
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
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
