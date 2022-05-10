use crate as creusot_contracts;
use crate::logic::*;
use crate::{Int, Model, Seq};
use creusot_contracts_proc::*;

use std::alloc::Allocator;
use std::slice::SliceIndex;

use std::ops::{Index, IndexMut};

pub use ::std::vec::from_elem;

impl<T, A: Allocator> Model for Vec<T, A> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
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
        pearlite! { seq[@self] === out }
    }

    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn resolve_elswhere(self, old: Seq<T>, fin: Seq<T>) -> bool {
        pearlite! { forall<i : Int> 0 <= i && !(i === @self) && i <= old.len() ==> old[i] === fin[i] }
    }
}

extern_spec! {
  #[creusot::extern_spec::impl_]
  #[requires(ix.in_bounds(@*self_))]
  #[ensures(ix.has_value(@*self_, *result))]
  #[ensures(ix.has_value(@^self_, ^result))]
  #[ensures(ix.resolve_elswhere(@*self_, @^self_))]
  #[ensures((@^self_).len() === (@*self_).len())]
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
    #[ensures(@result === (@*self_).len())]
    fn std::vec::Vec::len<T, A : Allocator>(self_ : &Vec<T, A>) -> usize
}

extern_spec! {
  #[ensures((@result).len() === 0)]
  fn std::vec::Vec::new<T>() -> Vec<T>
}

use std::ops::DerefMut;

extern_spec! {
    #[creusot::extern_spec::impl_]
    #[ensures(@*result === @*self_)]
    #[ensures(@^result === @^self_)]
    fn std::vec::Vec::deref_mut<T, A : Allocator>(self_: &mut Vec<T, A>) -> &mut [T]
}

extern_spec! {
    #[ensures((@result).len() === 0)]
    fn std::vec::Vec::with_capacity<T>(capacity: usize) -> Vec<T>
}

extern_spec! {
    #[ensures(@^self_ === (@*self_).push(v))]
    fn std::vec::Vec::push<T, A : Allocator>(self_: &mut Vec<T, A>, v: T)
}

extern_spec! {
  #[ensures((@result).len() === @n)]
  #[ensures(forall<i : Int> 0 <= i && i < @n ==> (@result)[i] === elem)]
  fn std::vec::from_elem<T : Clone>(elem : T, n : usize) -> Vec<T>
}

// impl<T> Vec<T> {
//     #[trusted]
//     #[ensures(match result {
//         Some(t) => *t === (@*self)[ix.into()],
//         None => (@*self).len() <= ix.into(),
//     })]
//     pub fn get(&self, ix: usize) -> Option<&T> {
//         self.0.get(ix)
//     }

//     #[trusted]
//     #[ensures(match result {
//         Some(t) => (@self) === (@^self).push(t),
//         None => (@self).len() === (@^self).len() && (@self).len() === 0
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
// #[ensures((@result).len() === @n)]
// #[ensures(forall<i : Int> 0 <= i && i < @n ==> (@result)[i] === elem)]
// pub fn from_elem<T: Clone>(elem: T, n: usize) -> Vec<T> {
//     panic!()
// }
