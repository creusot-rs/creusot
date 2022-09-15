use crate as creusot_contracts;
use crate::{
    logic::*,
    std::{iter::IteratorSpec, slice::SliceIndexSpec},
    Int, Model, Seq,
};
pub use ::std::vec::from_elem;
use creusot_contracts_proc::*;
use std::{
    alloc::Allocator,
    ops::{Deref, DerefMut, Index, IndexMut},
    vec::IntoIter,
};

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

                #[requires(@ix < (@self).len())]
                #[ensures(result == (@self)[@ix])]
                #[ensures(@^self == (@self).subsequence(0, @ix).concat((@self).subsequence(@ix + 1, (@self).len())))]
                #[ensures((@^self).len() == (@self).len() - 1)]
                fn remove(&mut self, ix: usize) -> T;

                #[ensures((@^self).len() == (@self).len() + 1)]
                #[ensures(forall<i: Int> 0 <= i && i < @index ==> (@^self)[i] == (@self)[i])]
                #[ensures((@^self)[@index] == element)]
                #[ensures(forall<i: Int> @index < i && i < (@^self).len() ==> (@^self)[i] == (@self)[i - 1])]
                fn insert(&mut self, index: usize, element: T);

                #[ensures(@result == @self)]
                fn into_iter(self) -> IntoIter<T, A>;
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

// Has to be placed outside because of limitations in the proc macro for extern spec
// that cannot properly prefix `Vec` with `std::vec::` inside `&'a Vec`
extern_spec! {
    impl<'a, T, A : Allocator> IntoIterator for &'a std::vec::Vec<T, A> {
        #[ensures(@result == @self)]
        fn into_iter(self) -> std::slice::Iter<'a, T>;
    }
}

#[trusted]
impl<T> Resolve for Vec<T> {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! { forall<i : Int> 0 <= i && i < (@self).len() ==> (@self)[i].resolve() }
    }
}

impl<T, A: Allocator> IteratorSpec for std::vec::IntoIter<T, A> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && @*self == Seq::EMPTY }
    }

    #[predicate]
    fn produces(self, visited: Seq<T>, rhs: Self) -> bool {
        pearlite! {
            (@self).len() == visited.len() + (@rhs).len() &&
            (@self).subsequence(visited.len(), (@self).len()).ext_eq(@rhs) &&
            (forall<i : Int> 0 <= i && i < visited.len() ==>
                (@self)[i] == visited[i])
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<T>, b: Self, bc: Seq<T>, c: Self) {}
}

impl<T, A: Allocator> Model for std::vec::IntoIter<T, A> {
    type ModelTy = Seq<T>;

    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}
