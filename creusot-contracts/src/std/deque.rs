use crate::{invariant::Invariant, logic::IndexLogic, std::alloc::Allocator, *};
use ::std::collections::vec_deque::{IntoIter, Iter};
pub use ::std::collections::VecDeque;

impl<T, A: Allocator> ShallowModel for VecDeque<T, A> {
    type ShallowModelTy = Seq<T>;

    #[ghost]
    #[trusted]
    #[open(self)]
    #[ensures(result.len() <= usize::MAX@)]
    fn shallow_model(self) -> Seq<T> {
        pearlite! { absurd }
    }
}

impl<'a, T> Invariant for Iter<'a, T> {}

impl<T, A: Allocator> ShallowModel for IntoIter<T, A> {
    type ShallowModelTy = Seq<T>;

    #[open(self)]
    #[ghost]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

impl<'a, T> ShallowModel for Iter<'a, T> {
    // TODO : This seems wrong
    type ShallowModelTy = &'a [T];

    #[ghost]
    #[open(self)]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    #[predicate]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && (*self)@@ == Seq::EMPTY }
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
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<T, A: Allocator> Invariant for IntoIter<T, A> {}

impl<T, A: Allocator> Iterator for IntoIter<T, A> {
    #[predicate]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && self@ == Seq::EMPTY }
    }

    #[predicate]
    #[open]
    fn produces(self, visited: Seq<T>, rhs: Self) -> bool {
        pearlite! {
            self@ == visited.concat(rhs@)
        }
    }

    #[law]
    #[open]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<T>, b: Self, bc: Seq<T>, c: Self) {}
}

impl<T, A: Allocator> IntoIterator for VecDeque<T, A> {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[predicate]
    #[open]
    fn into_iter_post(self, res: Self::IntoIter) -> bool {
        pearlite! { self@ == res@ }
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

// impl<T, A: Allocator> IntoIterator for &mut VecDeque<T, A> {
//     #[predicate]
//     #[open]
//     fn into_iter_pre(self) -> bool {
//         pearlite! { true }
//     }

//     #[predicate]
//     #[open]
//     fn into_iter_post(self, res: Self::IntoIter) -> bool {
//         pearlite! { self@ == res@@ }
//     }
// }

impl<T: DeepModel, A: Allocator> DeepModel for VecDeque<T, A> {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[ghost]
    #[trusted]
    #[open(self)]
    #[ensures(self.shallow_model().len() == result.len())]
    #[ensures(forall<i: Int> 0 <= i && i < self.shallow_model().len()
              ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { absurd }
    }
}

impl<T, A: Allocator> IndexLogic<Int> for VecDeque<T, A> {
    type Item = T;

    #[ghost]
    #[open]
    #[why3::attr = "inline:trivial"]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

impl<T, A: Allocator> IndexLogic<usize> for VecDeque<T, A> {
    type Item = T;

    #[ghost]
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
                #[ensures(result@.len() == 0)]
                fn new() -> Self;

                #[ensures(result@.len() == 0)]
                fn with_capacity(capacity: usize) -> Self;
            }

            impl<T, A: Allocator> VecDeque<T, A> {
                #[ensures(result@ == self@.len())]
                fn len(&self) -> usize;

                #[ensures(result == (self@.len() == 0))]
                fn is_empty(&self) -> bool;

                #[ensures((^self)@.len() == 0)]
                fn clear(&mut self);

                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(1, self@.len()) &&
                        self@ == Seq::singleton(t).concat((^self)@),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_front(&mut self) -> Option<T>;

                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(0, self@.len() - 1) &&
                        self@ == (^self)@.push(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_back(&mut self) -> Option<T>;

                #[ensures((^self)@.len() == self@.len() + 1)]
                #[ensures((^self)@ == Seq::singleton(value).concat(self@))]
                fn push_front(&mut self, value: T);

                #[ensures((^self)@ == self@.push(value))]
                fn push_back(&mut self, value: T);
            }
        }
    }
}
