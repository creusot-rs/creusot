use crate::{std::alloc::Allocator, *};
pub use ::std::collections::VecDeque;

impl<T, A: Allocator> ShallowModel for VecDeque<T, A> {
    type ShallowModelTy = Seq<T>;

    #[logic]
    #[trusted]
    #[ensures(result.len() <= @usize::MAX)]
    fn shallow_model(self) -> Seq<T> {
        pearlite! { absurd }
    }
}

impl<T: DeepModel, A: Allocator> DeepModel for VecDeque<T, A> {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[logic]
    #[trusted]
    #[ensures(self.shallow_model().len() == result.len())]
    #[ensures(forall<i: Int> 0 <= i && i < self.shallow_model().len()
              ==> result[i] == self@[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { absurd }
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

                #[ensures((@^self).len() == 0)]
                fn clear(&mut self);

                #[ensures(match result {
                    Some(t) =>
                        @^self == self@.subsequence(1, self@.len()) &&
                        self@ == Seq::singleton(t).concat(@^self),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_front(&mut self) -> Option<T>;

                #[ensures(match result {
                    Some(t) =>
                        @^self == self@.subsequence(0, self@.len() - 1) &&
                        self@ == (@^self).push(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop_back(&mut self) -> Option<T>;

                #[ensures((@^self).len() == self@.len() + 1)]
                #[ensures((@^self) == Seq::singleton(value).concat(self@))]
                fn push_front(&mut self, value: T);

                #[ensures(@^self == self@.push(value))]
                fn push_back(&mut self, value: T);
            }
        }
    }
}
