use crate as creusot_contracts;
use crate::logic::*;
use crate::{Int, Model, Seq};
use creusot_contracts_proc::*;

use std::alloc::Allocator;

use crate::std::slice::SliceIndexSpec;
use std::ops::{Deref, DerefMut, Index, IndexMut};

pub use ::std::vec::from_elem;

impl<T, A: Allocator> Model for Vec<T, A> {
    type ModelTy = Seq<T>;

    #[logic]
    #[trusted]
    #[ensures(result.len() <= @isize::MAX)]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}

extern_spec! {
  #[creusot::extern_spec::impl_]
  #[requires(ix.in_bounds(@*self_))]
  #[ensures(ix.has_value(@*self_, *result))]
  #[ensures(ix.has_value(@^self_, ^result))]
  #[ensures(ix.resolve_elswhere(@*self_, @^self_))]
  #[ensures((@^self_).len() == (@*self_).len())]
  fn std::vec::Vec::index_mut<T, I, A>(self_ : &mut Vec<T, A>, ix: I) -> &mut <Vec<T, A> as Index<I>>::Output
    where A : Allocator,
          I : SliceIndexSpec<[T]>,
}

extern_spec! {
  #[creusot::extern_spec::impl_]
  #[requires(ix.in_bounds(@*self_))]
  #[ensures(ix.has_value(@*self_, *result))]
  fn std::vec::Vec::index<T, I, A>(self_ : &Vec<T, A>, ix: I) -> &<Vec<T, A> as Index<I>>::Output
    where A : Allocator,
          I : SliceIndexSpec<[T]>,
}

extern_spec! {
    #[ensures(@result == (@*self_).len())]
    fn std::vec::Vec::len<T, A : Allocator>(self_ : &Vec<T, A>) -> usize
}

extern_spec! {
  #[ensures((@result).len() == 0)]
  fn std::vec::Vec::new<T>() -> Vec<T>
}

extern_spec! {
    #[creusot::extern_spec::impl_]
    #[ensures(@*result == @*self_)]
    fn std::vec::Vec::deref<T, A : Allocator>(self_: &Vec<T, A>) -> &[T]
}

extern_spec! {
    #[creusot::extern_spec::impl_]
    #[ensures(@*result == @*self_)]
    #[ensures(@^result == @^self_)]
    fn std::vec::Vec::deref_mut<T, A : Allocator>(self_: &mut Vec<T, A>) -> &mut [T]
}

extern_spec! {
    #[ensures((@result).len() == 0)]
    fn std::vec::Vec::with_capacity<T>(capacity: usize) -> Vec<T>
}

extern_spec! {
    #[ensures(@^self_ == (@*self_).push(v))]
    fn std::vec::Vec::push<T, A : Allocator>(self_: &mut Vec<T, A>, v: T)
}

extern_spec! {
  #[ensures((@result).len() == @n)]
  #[ensures(forall<i : Int> 0 <= i && i < @n ==> (@result)[i] == elem)]
  fn std::vec::from_elem<T : Clone>(elem : T, n : usize) -> Vec<T>
}

extern_spec! {
    #[ensures(match result {
        Some(t) =>
            (@^self_) == (@*self_).subsequence(0, (@*self_).len() - 1) &&
            (@self_) == (@^self_).push(t),
        None => (@self_).len() == (@^self_).len() && (@*self_).len() == 0
    })]
    fn std::vec::Vec::pop<T, A : Allocator>(self_ : &mut Vec<T, A>) -> Option<T>
}

// impl<T> Vec<T> {
//     #[trusted]
//     #[ensures(match result {
//         Some(t) => *t == (@*self)[ix.into()],
//         None => (@*self).len() <= ix.into(),
//     })]
//     pub fn get(&self, ix: usize) -> Option<&T> {
//         self.0.get(ix)
//     }

//     #[trusted]
//     #[ensures(match result {
//         Some(t) => (@self) == (@^self).push(t),
//         None => (@self).len() == (@^self).len() && (@self).len() == 0
//     })]
//     pub fn pop(&mut self) -> Option<T> {
//         self.0.pop()
//     }
// }

// impl<T: Clone> Clone for Vec<T> {
//     #[trusted]
//     fn clone(&self) -> Self {
//         panic!()
//         // Vec(self.0.iter().map(|r : &T| r.clone()).collect())
//     }
// }

unsafe impl<T> Resolve for Vec<T> {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! { forall<i : Int> 0 <= i && i < (@self).len() ==> (@self)[i].resolve() }
    }
}

// #[trusted]
// #[ensures((@result).len() == @n)]
// #[ensures(forall<i : Int> 0 <= i && i < @n ==> (@result)[i] == elem)]
// pub fn from_elem<T: Clone>(elem: T, n: usize) -> Vec<T> {
//     panic!()
// }
