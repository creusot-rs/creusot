use crate::{invariant::Invariant, logic::IndexLogic, std::alloc::Allocator, *};
use ::std::collections::vec_deque::Iter;
pub use ::std::collections::VecDeque;

impl<T, A: Allocator> View for VecDeque<T, A> {
    type ViewTy = Seq<T>;

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(result.len() <= usize::MAX@)]
    fn view(self) -> Seq<T> {
        pearlite! { absurd }
    }
}

impl<T: EqModel, A: Allocator> EqModel for VecDeque<T, A> {
    type EqModelTy = Seq<T::EqModelTy>;

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i: Int> 0 <= i && i < self.view().len()
              ==> result[i] == self[i].eq_model())]
    fn eq_model(self) -> Self::EqModelTy {
        pearlite! { absurd }
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
                        self@ == Seq::singleton(t).concat((^self)@),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_front(&mut self) -> Option<T>;

                #[pure]
                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(0, self@.len() - 1) &&
                        self@ == (^self)@.push(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_back(&mut self) -> Option<T>;

                #[terminates] // can OOM
                #[ensures((^self)@.len() == self@.len() + 1)]
                #[ensures((^self)@ == Seq::singleton(value).concat(self@))]
                fn push_front(&mut self, value: T);

                #[terminates] // can OOM
                #[ensures((^self)@ == self@.push(value))]
                fn push_back(&mut self, value: T);
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
    #[open(self)]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        absurd
    }
}

impl<'a, T> Invariant for Iter<'a, T> {}

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
