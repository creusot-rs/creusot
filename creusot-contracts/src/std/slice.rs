use crate as creusot_contracts;
use creusot_contracts_proc::*;

extern_spec! {
  #[ensures((@s).len() === @result)]
  fn <[T]>::len<T>(s: &[T]) -> usize
}

use crate::logic::OrdLogic;
use crate::std::vec::SliceIndexSpec;
use std::ops::{Index, IndexMut};
use std::slice::SliceIndex;

extern_spec! {
  #[requires(@i < (@s).len())]
  #[requires(@j < (@s).len())]
  #[ensures((@^s).exchange(@*s, @i, @j))]
  fn <[T]>::swap<T>(s: &mut [T], i: usize, j: usize)
}

extern_spec! {
  #[requires(ix.in_bounds(@*self_))]
 // #[ensures(match result {
 //      Some(t) => *t === (@*self)[ix.into()],
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
  // #[ensures((@^self_).len() === (@*self_).len())]
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
