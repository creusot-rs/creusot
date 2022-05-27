use crate as creusot_contracts;
use crate::logic::OrdLogic;
use crate::std::default::DefaultSpec;
use crate::{Int, Model, Seq};
use creusot_contracts_proc::*;
use std::ops::{Index, IndexMut};
use std::slice::SliceIndex;

impl<T> Model for [T] {
    type ModelTy = Seq<T>;

    // TODO: remove the trusted attribute, and use slice_model as the definition of this.
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
#[creusot::builtins = "prelude.Prelude.id"]
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

extern_spec! {
  #[ensures((@s).len() == @result)]
  fn <[T]>::len<T>(s: &[T]) -> usize
}

extern_spec! {
  #[requires(@i < (@s).len())]
  #[requires(@j < (@s).len())]
  #[ensures((@^s).exchange(@*s, @i, @j))]
  fn <[T]>::swap<T>(s: &mut [T], i: usize, j: usize)
}

extern_spec! {
  #[requires(ix.in_bounds(@*self_))]
 // #[ensures(match result {
 //      Some(t) => *t == (@*self)[ix.into()],
 //      None => (@*self).len() <= ix.into(),
 //  })]
  fn <[T]>::get<T, I : SliceIndexSpec<[T]>>(self_: &[T], ix: I) -> Option<&<I as SliceIndex<[T]>>::Output>
}

extern_spec! {
  #[creusot::extern_spec::impl_]
  // #[requires(ix.in_bounds(@*self_))]
  // #[ensures(ix.has_value(@*self_, *result))]
  // #[ensures(ix.has_value(@^self_, ^result))]
  // #[ensures(ix.resolve_elswhere(@*self_, @^self_))]
  // #[ensures((@^self_).len() == (@*self_).len())]
  fn <[T]>::index_mut<T, I>(self_ : &mut [T], ix: I) -> &mut <[T] as Index<I>>::Output
    where I : SliceIndexSpec<[T]>,
}

extern_spec! {
  #[creusot::extern_spec::impl_]
  // #[requires(ix.in_bounds(@*self_))]
  // #[ensures(ix.has_value(@*self_, *result))]
  fn <[T]>::index<T, I>(self_ : &[T], ix: I) -> &<[T] as Index<I>>::Output
    where I : SliceIndexSpec<[T]>,
}

extern_spec! {
    #[ensures(result == None ==> (@s).len() == 0 && ^s == *s && @*s == Seq::EMPTY)]
    #[ensures(forall<first: &mut T, tail: &mut [T]>
              result == Some((first, tail))
            && *first == (@*s)[0] && ^first == (@^s)[0]
            && (@*s).len() > 0 && (@^s).len() > 0
            && @*tail == (@*s).tail()
            && @^tail == (@^s).tail())]
    fn <[T]>::split_first_mut<'a, T>(s: &'a mut [T]) -> Option<(&'a mut T, &'a mut [T])>
}
