use crate as creusot_contracts;
use crate::{
    logic::*,
    std::{default::DefaultSpec, iter::IteratorSpec},
    Int, Model, Seq,
};
use creusot_contracts_proc::*;
use std::{
    ops::{Index, IndexMut, Range, RangeFrom, RangeFull, RangeTo, RangeToInclusive},
    slice::{Iter, IterMut, SliceIndex},
};

impl<T> Model for [T] {
    type ModelTy = Seq<T>;

    // We define this as trusted because builtins and ensures are incompatible
    #[logic]
    #[trusted]
    #[ensures(result.len() <= @usize::MAX)]
    #[ensures(result == slice_model(self))]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}

#[logic]
#[trusted]
#[creusot::builtins = "prelude.Slice.id"]
fn slice_model<T>(_: [T]) -> Seq<T> {
    pearlite! { absurd }
}

impl<T> DefaultSpec for &mut [T] {
    #[logic]
    #[trusted]
    #[ensures(@*result == Seq::EMPTY)]
    #[ensures(@^result == Seq::EMPTY)]
    fn default_log() -> Self {
        absurd
    }
}

impl<T> DefaultSpec for &[T] {
    #[logic]
    #[trusted]
    #[ensures(@*result == Seq::EMPTY)]
    fn default_log() -> Self {
        absurd
    }
}

pub(crate) trait SliceIndexSpec<T: ?Sized>: SliceIndex<T>
where
    T: Model,
{
    #[predicate]
    fn in_bounds(self, seq: T::ModelTy) -> bool;

    #[predicate]
    fn has_value(self, seq: T::ModelTy, out: Self::Output) -> bool;

    #[predicate]
    fn resolve_elswhere(self, old: T::ModelTy, fin: T::ModelTy) -> bool;
}

impl<T> SliceIndexSpec<[T]> for usize {
    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { @self < seq.len() }
    }

    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn has_value(self, seq: Seq<T>, out: T) -> bool {
        pearlite! { seq[@self] == out }
    }

    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i : Int> 0 <= i && i != @self && i < old.len() ==> old[i] == fin[i] }
    }
}

impl<T> SliceIndexSpec<[T]> for Range<usize> {
    #[predicate]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { @self.start <= @self.end && @self.end <= seq.len() }
    }

    #[predicate]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(@self.start, @self.end) == @out }
    }

    #[predicate]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i : Int> 0 <= i && (i < @self.start || @self.end <= i) && i < old.len()
            ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeTo<usize> {
    #[predicate]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { @self.end <= seq.len() }
    }

    #[predicate]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(0, @self.end) == @out }
    }

    #[predicate]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i : Int> @self.end <= i && i < old.len() ==> old[i] == fin[i] }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeFrom<usize> {
    #[predicate]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { @self.start <= seq.len() }
    }

    #[predicate]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(@self.start, seq.len()) == @out }
    }

    #[predicate]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! {
            forall<i : Int> 0 <= i && i < @self.start && i < old.len() ==> old[i] == fin[i]
        }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeFull {
    #[predicate]
    fn in_bounds(self, _seq: Seq<T>) -> bool {
        pearlite! { true }
    }

    #[predicate]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq == @out }
    }

    #[predicate]
    fn resolve_elswhere(self, _old: Seq<T>, _fin: Seq<T>) -> bool {
        pearlite! { true }
    }
}

impl<T> SliceIndexSpec<[T]> for RangeToInclusive<usize> {
    #[predicate]
    fn in_bounds(self, seq: Seq<T>) -> bool {
        pearlite! { @self.end < seq.len() }
    }

    #[predicate]
    fn has_value(self, seq: Seq<T>, out: [T]) -> bool {
        pearlite! { seq.subsequence(0, @self.end + 1) == @out }
    }

    #[predicate]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i : Int> @self.end < i && i < old.len() ==> old[i] == fin[i] }
    }
}

extern_spec! {
    impl<T> [T] {
        #[ensures((@self).len() == @result)]
        fn len(&self) -> usize;

        #[requires(@i < (@self).len())]
        #[requires(@j < (@self).len())]
        #[ensures((@^self).exchange(@*self, @i, @j))]
        fn swap(&mut self, i: usize, j: usize);

        #[ensures(
            ix.in_bounds(@*self)
            ==> exists<r: &<I as SliceIndex<[T]>>::Output> result == Some(r)
                && ix.has_value(@*self_, *r)
        )]
        #[ensures(ix.in_bounds(@*self) || result == None)]
        fn get<I : SliceIndexSpec<[T]>>(&self, ix: I) -> Option<&<I as SliceIndex<[T]>>::Output>;

        #[requires(@mid <= (@self).len())]
        #[ensures({
            let (l,r) = result;  let sl = (@self).len();
            ((@^self).len() == sl) &&
            (@self).subsequence(0, @mid).ext_eq(@l) &&
            (@self).subsequence(@mid, sl).ext_eq(@r) &&
            (@^self).subsequence(0, @mid).ext_eq(@^l) &&
            (@^self).subsequence(@mid, sl).ext_eq(@^r)
        })]
        fn split_at_mut(&mut self, mid: usize) -> (&mut [T], &mut [T]);

        #[ensures(result == None ==> (@self).len() == 0 && ^self == *self && @*self == Seq::EMPTY)]
        #[ensures(forall<first: &mut T, tail: &mut [T]>
                  result == Some((first, tail))
                && *first == (@*self)[0] && ^first == (@^self)[0]
                && (@*self).len() > 0 && (@^self).len() > 0
                && @*tail == (@*self).tail()
                && @^tail == (@^self).tail())]
        fn split_first_mut(&mut self) -> Option<(&mut T, &mut [T])>;

        #[ensures(match result {
            Some(r) => {
                * r == (@**self)[0] &&
                ^ r == (@^*self)[0] &&
                (@**self).len() > 0 && // ^*s.len == **s.len ? (i dont think so)
                (@^*self).len() > 0 &&
                (@*^self).ext_eq((@**self).tail()) && (@^^self).ext_eq((@^*self).tail())
            }
            None => ^self == * self && (@**self).len() == 0
        })]
        fn take_first_mut<'a>(self_: &mut &'a mut [T]) -> Option<&'a mut T>;

        #[ensures(@result == @self)]
        fn iter(&self) -> Iter<'_, T>;

        #[ensures(*@result == @self)]
        #[ensures(^@result == @^self)]
        #[ensures((^@result).len() == (@self).len())]
        fn iter_mut(&mut self) -> IterMut<'_, T>;
    }

    impl<'a, T> IntoIterator for &'a [T] {
        #[ensures(@result == @self)]
        fn into_iter(self) -> Iter<'a, T>;
    }

    impl<T, I> IndexMut<I> for [T]
        where I : SliceIndexSpec<[T]> {
       #[requires(ix.in_bounds(@*self))]
       #[ensures(ix.has_value(@*self, *result))]
       #[ensures(ix.has_value(@^self, ^result))]
       #[ensures(ix.resolve_elswhere(@*self, @^self))]
       #[ensures((@^self).len() == (@*self).len())]
        fn index_mut(&mut self, ix: I) -> &mut <[T] as Index<I>>::Output;
    }

    impl<T, I> Index<I> for [T]
    where I : SliceIndexSpec<[T]> {
      #[requires(ix.in_bounds(@*self))]
      #[ensures(ix.has_value(@*self, *result))]
      fn index(&self, ix: I) -> &<[T] as Index<I>>::Output;
    }
}

impl<T> Model for Iter<'_, T> {
    type ModelTy = Seq<T>;

    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

impl<'a, T> Model for IterMut<'a, T> {
    type ModelTy = &'a mut Seq<T>;

    #[logic]
    #[trusted]
    #[ensures((^result).len() == result.len())]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

impl<'a, T> IteratorSpec for Iter<'a, T> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && @*self == Seq::EMPTY }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, rhs: Self) -> bool {
        pearlite! {
            (@self).len() == visited.len() + (@rhs).len() &&
            (@self).subsequence(visited.len(), (@self).len()).ext_eq(@rhs) &&
            (forall<i : Int> 0 <= i && i < visited.len() ==>
                (@self)[i] == *visited[i])
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<'a, T> IteratorSpec for IterMut<'a, T> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && *@*self == Seq::EMPTY }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            (@self).len() == visited.len() + (@tl).len() &&
            (^@self).len() == visited.len() + (^@tl).len() &&
            (@self).subsequence(visited.len(), (@self).len()).ext_eq(*@tl) &&
            (^@self).subsequence(visited.len(), (^@self).len()).ext_eq(^@tl)&&
            (forall<i : Int> 0 <= i && i < visited.len() ==>
                (@self)[i] == *visited[i] && (^@self)[i] == ^visited[i])
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
