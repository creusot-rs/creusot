#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{logic::ops::IndexLogic, *};
#[cfg(feature = "nightly")]
use ::std::alloc::Allocator;
pub use ::std::collections::VecDeque;
use ::std::{
    collections::vec_deque::Iter,
    ops::{Index, IndexMut},
};

#[cfg(feature = "nightly")]
impl<T, A: Allocator> View for VecDeque<T, A> {
    type ViewTy = Seq<T>;

    #[trusted]
    #[logic(opaque)]
    #[ensures(result.len() <= usize::MAX@)]
    fn view(self) -> Seq<T> {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel, A: Allocator> DeepModel for VecDeque<T, A> {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[trusted]
    #[logic(opaque)]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i> 0 <= i && i < self.view().len()
              ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> IndexLogic<Int> for VecDeque<T, A> {
    type Item = T;

    #[logic(open, inline)]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> IndexLogic<usize> for VecDeque<T, A> {
    type Item = T;

    #[logic(open, inline)]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> Resolve for VecDeque<T> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        pearlite! { forall<i> 0 <= i && i < self@.len() ==> resolve(self[i]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

extern_spec! {
    mod std {
        mod collections {
            impl<T> VecDeque<T> {
                #[check(ghost)]
                #[ensures(result@.len() == 0)]
                fn new() -> Self;

                #[check(terminates)] // can OOM
                #[ensures(result@.len() == 0)]
                fn with_capacity(capacity: usize) -> Self;
            }

            impl<T, A: Allocator> VecDeque<T, A> {
                #[check(ghost)]
                #[ensures(result@ == self@.len())]
                fn len(&self) -> usize;

                #[check(ghost)]
                #[ensures(result == (self@.len() == 0))]
                fn is_empty(&self) -> bool;

                #[check(ghost)]
                #[ensures((^self)@.len() == 0)]
                fn clear(&mut self);

                #[check(ghost)]
                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(1, self@.len()) &&
                        self@ == (^self)@.push_front(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_front(&mut self) -> Option<T>;

                #[check(ghost)]
                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(0, self@.len() - 1) &&
                        self@ == (^self)@.push_back(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_back(&mut self) -> Option<T>;

                #[check(terminates)] // can OOM
                #[ensures((^self)@.len() == self@.len() + 1)]
                #[ensures((^self)@ == self@.push_front(value))]
                fn push_front(&mut self, value: T);

                #[check(terminates)] // can OOM
                #[ensures((^self)@ == self@.push_back(value))]
                fn push_back(&mut self, value: T);
            }
        }
    }

    impl<T, A: Allocator> Index<usize> for VecDeque<T, A> {
        #[ensures(*result == self@[i@])]
        fn index(&self, i: usize) -> &T;
    }

    impl<T, A: Allocator> IndexMut<usize> for VecDeque<T, A> {
        #[ensures(*result == (*self)@[i@])]
        #[ensures(^result == (^self)@[i@])]
        fn index_mut(&mut self, i: usize) -> &mut T;
    }

    impl<'a, T, A: Allocator> IntoIterator for &'a VecDeque<T, A> {
        #[ensures(self@ == result@@)]
        fn into_iter(self) -> Iter<'a, T>;
    }
}

impl<'a, T> View for Iter<'a, T> {
    type ViewTy = &'a [T];

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && (*self@)@ == Seq::empty() }
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

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
mod impls {
    use super::*;
    impl<T> View for VecDeque<T> {
        type ViewTy = Seq<T>;
    }
    impl<T: DeepModel> DeepModel for VecDeque<T> {
        type DeepModelTy = Seq<T::DeepModelTy>;
    }
    impl<T> IndexLogic<Int> for VecDeque<T> {
        type Item = T;
    }
    impl<T> IndexLogic<usize> for VecDeque<T> {
        type Item = T;
    }
}
