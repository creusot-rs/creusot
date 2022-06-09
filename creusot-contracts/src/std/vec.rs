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
    #[ensures(result.len() <= @usize::MAX)]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}

extern_spec! {
    mod std {
        mod vec {
            impl<T> Vec<T> {
                #[ensures((@result).len() == 0)]
                fn new() -> Vec<T>;

                #[ensures((@result).len() == 0)]
                fn with_capacity(capacity: usize) -> Vec<T>;
            }

            impl<T, A : Allocator> Vec<T, A> {
                #[ensures(@result == (@*self).len())]
                fn len(&self) -> usize;

                #[ensures(@^self == (@*self).push(v))]
                fn push(&mut self, v: T);

                #[ensures(match result {
                    Some(t) =>
                        @^self == (@*self).subsequence(0, (@*self).len() - 1) &&
                        @*self == (@^self).push(t),
                    None => *self == ^self && (@*self).len() == 0
                })]
                fn pop(&mut self) -> Option<T>;
            }

            impl<T, I : SliceIndexSpec<[T]>, A : Allocator> IndexMut<I> for Vec<T, A> {
                #[requires(ix.in_bounds(@*self))]
                #[ensures(ix.has_value(@*self, *result))]
                #[ensures(ix.has_value(@^self, ^result))]
                #[ensures(ix.resolve_elswhere(@*self, @^self))]
                #[ensures((@^self).len() == (@*self).len())]
                fn index_mut(&mut self, ix: I) -> &mut <Vec<T, A> as Index<I>>::Output;
            }

            impl<T, I : SliceIndexSpec<[T]>, A : Allocator> Index<I> for Vec<T, A> {
                #[requires(ix.in_bounds(@*self))]
                #[ensures(ix.has_value(@*self, *result))]
                fn index(&self, ix: I) -> & <Vec<T, A> as Index<I>>::Output;
            }

            impl<T, A : Allocator> Deref for Vec<T, A> {
                #[ensures(@*result == @*self)]
                fn deref(&self) -> &[T];
            }

            impl<T, A : Allocator> DerefMut for Vec<T, A> {
                #[ensures(@*result == @*self)]
                #[ensures(@^result == @^self)]
                fn deref_mut(&mut self) -> &mut [T];
            }

            #[ensures((@result).len() == @n)]
            #[ensures(forall<i : Int> 0 <= i && i < @n ==> (@result)[i] == elem)]
            fn from_elem<T : Clone>(elem : T, n : usize) -> Vec<T>;

        }
    }
}

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
