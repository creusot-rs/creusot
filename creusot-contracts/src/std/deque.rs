use crate::{logic::ops::IndexLogic, resolve::structural_resolve, std::alloc::Allocator, *};
pub use ::std::collections::VecDeque;
use ::std::{
    collections::vec_deque::Iter,
    ops::{Index, IndexMut},
};

impl<T, A: Allocator> View for VecDeque<T, A> {
    type ViewTy = Seq<T>;

    #[logic]
    #[trusted]
    #[ensures(result.len() <= usize::MAX@)]
    fn view(self) -> Seq<T> {
        dead
    }
}

impl<T: DeepModel, A: Allocator> DeepModel for VecDeque<T, A> {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i: Int> 0 <= i && i < self.view().len()
              ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl<T, A: Allocator> IndexLogic<Int> for VecDeque<T, A> {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, A: Allocator> IndexLogic<usize> for VecDeque<T, A> {
    type Item = T;

    #[logic]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

impl<T> Resolve for VecDeque<T> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! { forall<i : Int> 0 <= i && i < self@.len() ==> resolve(&self[i]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

extern_spec! {
    mod std {
        mod collections {
            impl<T> VecDeque<T> {
                #[pure]
                #[ensures(result@.len() == 0)]
                fn new() -> Self;

                #[terminates] // can OOM
                #[ensures(result@.len() == 0)]
                fn with_capacity(capacity: usize) -> Self;
            }

            impl<T, A: Allocator> VecDeque<T, A> {
                #[pure]
                #[ensures(result@ == self@.len())]
                fn len(&self) -> usize;

                #[pure]
                #[ensures(result == (self@.len() == 0))]
                fn is_empty(&self) -> bool;

                #[pure]
                #[ensures((^self)@.len() == 0)]
                fn clear(&mut self);

                #[pure]
                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(1, self@.len()) &&
                        self@ == (^self)@.push_front(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_front(&mut self) -> Option<T>;

                #[pure]
                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(0, self@.len() - 1) &&
                        self@ == (^self)@.push_back(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_back(&mut self) -> Option<T>;

                #[terminates] // can OOM
                #[ensures((^self)@.len() == self@.len() + 1)]
                #[ensures((^self)@ == self@.push_front(value))]
                fn push_front(&mut self, value: T);

                #[terminates] // can OOM
                #[ensures((^self)@ == self@.push_back(value))]
                fn push_back(&mut self, value: T);
            }

            impl<T, A: Allocator> Index<usize> for VecDeque<T> {
                #[ensures(*result == self@[i@])]
                fn index(&self, i: usize) -> &T;
            }

            impl<T, A: Allocator> IndexMut<usize> for VecDeque<T> {
                #[ensures(*result == (*self)@[i@])]
                #[ensures(^result == (^self)@[i@])]
                fn index_mut(&mut self, i: usize) -> &mut T;
            }
        }
    }
}

impl<T, A: Allocator> IntoIterator for &VecDeque<T, A> {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self@ == res@@ }
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
