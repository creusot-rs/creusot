#[cfg(creusot)]
use crate::{invariant::inv, resolve::structural_resolve, std::slice::SliceIndexSpec};
use crate::{logic::ops::IndexLogic, prelude::*};
use alloc::vec::*;
#[cfg(feature = "nightly")]
use core::alloc::Allocator;
use core::ops::{Deref, DerefMut, Index, IndexMut};

#[cfg(feature = "nightly")]
impl<T, A: Allocator> View for Vec<T, A> {
    type ViewTy = Seq<T>;

    #[trusted]
    #[logic(opaque)]
    #[ensures(result.len() <= usize::MAX@)]
    fn view(self) -> Seq<T> {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel, A: Allocator> DeepModel for Vec<T, A> {
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
impl<T, A: Allocator> IndexLogic<Int> for Vec<T, A> {
    type Item = T;

    #[logic(open, inline)]
    fn index_logic(self, ix: Int) -> Self::Item {
        pearlite! { self@[ix] }
    }
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> IndexLogic<usize> for Vec<T, A> {
    type Item = T;

    #[logic(open, inline)]
    fn index_logic(self, ix: usize) -> Self::Item {
        pearlite! { self@[ix@] }
    }
}

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
impl<T> IndexLogic<Int> for Vec<T> {
    type Item = T;
}

#[cfg(not(feature = "nightly"))]
impl<T> IndexLogic<usize> for Vec<T> {
    type Item = T;
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> Resolve for Vec<T, A> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn resolve(self) -> bool {
        pearlite! { forall<i> 0 <= i && i < self@.len() ==> resolve(self[i]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> Invariant for Vec<T, A> {
    #[logic(open, prophetic)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { inv(self@) }
    }
}

extern_spec! {
    mod alloc {
        mod vec {
            impl<T> Vec<T> {
                #[check(ghost)]
                #[ensures(result@.len() == 0)]
                fn new() -> Vec<T>;

                #[check(terminates)] // can OOM
                #[ensures(result@.len() == 0)]
                fn with_capacity(capacity: usize) -> Vec<T>;
            }
            impl<T, A: Allocator> Vec<T, A> {
                #[check(ghost)]
                #[ensures(result@ == self@.len())]
                fn len(&self) -> usize;

                #[check(terminates)] // can OOM
                #[ensures((^self)@ == self@.push_back(v))]
                fn push(&mut self, v: T);

                #[check(ghost)]
                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(0, self@.len() - 1) &&
                        self@ == (^self)@.push_back(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop(&mut self) -> Option<T>;

                #[check(ghost)]
                #[requires(ix@ < self@.len())]
                #[ensures(result == self[ix@])]
                #[ensures((^self)@ == self@.subsequence(0, ix@).concat(self@.subsequence(ix@ + 1, self@.len())))]
                #[ensures((^self)@.len() == self@.len() - 1)]
                fn remove(&mut self, ix: usize) -> T;

                #[check(terminates)] // can OOM
                #[ensures((^self)@.len() == self@.len() + 1)]
                #[ensures(forall<i> 0 <= i && i < index@ ==> (^self)[i] == self[i])]
                #[ensures((^self)[index@] == element)]
                #[ensures(forall<i> index@ < i && i < (^self)@.len() ==> (^self)[i] == self[i - 1])]
                fn insert(&mut self, index: usize, element: T);

                #[check(ghost)]
                #[ensures(result@ >= self@.len())]
                fn capacity(&self) -> usize;

                #[check(terminates)] // can OOM
                #[ensures((^self)@ == self@)]
                fn reserve(&mut self, additional: usize);

                #[check(terminates)] // can OOM
                #[ensures((^self)@ == self@)]
                fn reserve_exact(&mut self, additional: usize);

                #[check(ghost)]
                #[ensures((^self)@ == self@)]
                fn shrink_to_fit(&mut self);

                #[check(ghost)]
                #[ensures((^self)@ == self@)]
                fn shrink_to(&mut self, min_capacity: usize);

                #[check(ghost)]
                #[ensures((^self)@.len() == 0)]
                fn clear(&mut self);
            }

            impl<T, A: Allocator> Extend<T> for Vec<T, A> {
                #[requires(I::into_iter.precondition((iter,)))]
                #[ensures(exists<start_: I::IntoIter, done: &mut I::IntoIter, prod: Seq<T>>
                    inv(start_) && inv(done) && inv(prod) &&
                    I::into_iter.postcondition((iter,), start_) &&
                    done.completed() && start_.produces(prod, *done) && (^self)@ == self@.concat(prod)
                )]
                fn extend<I: IntoIterator<Item = T, IntoIter: IteratorSpec>>(&mut self, iter: I);
            }

            impl<T, I: SliceIndexSpec<[T]>, A: Allocator> IndexMut<I> for Vec<T, A> {
                #[check(ghost)]
                #[requires(ix.in_bounds(self@))]
                #[ensures(ix.has_value(self@, *result))]
                #[ensures(ix.has_value((^self)@, ^result))]
                #[ensures(ix.resolve_elswhere(self@, (^self)@))]
                #[ensures((^self)@.len() == self@.len())]
                fn index_mut(&mut self, ix: I) -> &mut <Vec<T, A> as Index<I>>::Output;
            }

            impl<T, I: SliceIndexSpec<[T]>, A: Allocator> Index<I> for Vec<T, A> {
                #[check(ghost)]
                #[requires(ix.in_bounds(self@))]
                #[ensures(ix.has_value(self@, *result))]
                fn index(&self, ix: I) -> & <Vec<T, A> as Index<I>>::Output;
            }

            impl<T, A: Allocator> Deref for Vec<T, A> {
                #[check(ghost)]
                #[ensures(result@ == self@)]
                fn deref(&self) -> &[T];
            }

            impl<T, A: Allocator> DerefMut for Vec<T, A> {
                #[check(ghost)]
                #[ensures(result@ == self@)]
                #[ensures((^result)@ == (^self)@)]
                fn deref_mut(&mut self) -> &mut [T];
            }

            #[ensures(result@.len() == n@)]
            #[ensures(forall<i> 0 <= i && i < n@ ==> result[i] == elem)]
            fn from_elem<T: Clone>(elem: T, n: usize) -> Vec<T>;
        }
    }

    impl<T, A: Allocator> IntoIterator for Vec<T, A> {
        #[check(ghost)]
        #[ensures(self@ == result@)]
        fn into_iter(self) -> IntoIter<T, A>;
    }

    impl<'a, T, A: Allocator> IntoIterator for &'a Vec<T, A> {
        #[check(ghost)]
        #[ensures(self@ == result@@)]
        fn into_iter(self) -> core::slice::Iter<'a, T>;
    }

    impl<'a, T, A: Allocator> IntoIterator for &'a mut Vec<T, A> {
        #[check(ghost)]
        #[ensures(self@ == result@@)]
        fn into_iter(self) -> core::slice::IterMut<'a, T>;
    }

    impl<T> Default for Vec<T> {
        #[check(ghost)]
        #[ensures(result@ == Seq::empty())]
        fn default() -> Vec<T>;
    }

    impl<T: Clone, A: Allocator + Clone> Clone for Vec<T, A> {
        #[check(terminates)]
        #[ensures(self@.len() == result@.len())]
        #[ensures(forall<i> 0 <= i && i < self@.len() ==>
            T::clone.postcondition((&self@[i],), result@[i]))]
        fn clone(&self) -> Vec<T, A>;
    }
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> View for IntoIter<T, A> {
    type ViewTy = Seq<T>;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> Resolve for IntoIter<T, A> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        pearlite! { forall<i> 0 <= i && i < self@.len() ==> resolve(self@[i]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

#[cfg(feature = "nightly")]
impl<T, A: Allocator> IteratorSpec for IntoIter<T, A> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { resolve(self) && self@ == Seq::empty() }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<T>, rhs: Self) -> bool {
        pearlite! {
            self@ == visited.concat(rhs@)
        }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<T>, b: Self, bc: Seq<T>, c: Self) {}
}

impl<T> FromIteratorSpec<T> for Vec<T> {
    #[logic(open)]
    fn from_iter_post(prod: Seq<T>, res: Self) -> bool {
        pearlite! { prod == res@ }
    }
}

/// Dummy impls that don't use the unstable trait Allocator
#[cfg(not(feature = "nightly"))]
mod impls {
    use crate::prelude::*;
    use alloc::vec::*;

    impl<T> View for Vec<T> {
        type ViewTy = Seq<T>;
    }

    impl<T: DeepModel> DeepModel for Vec<T> {
        type DeepModelTy = Seq<T::DeepModelTy>;
    }
    impl<T> Resolve for Vec<T> {}
    impl<T> Invariant for Vec<T> {}
    impl<T> View for IntoIter<T> {
        type ViewTy = Seq<T>;
    }
    impl<T> Resolve for IntoIter<T> {}
    impl<T> IteratorSpec for IntoIter<T> {}
}

/// Creusot-friendly replacement of `vec!`
///
/// The std vec macro uses special magic to construct the array argument
/// to `Box::new` directly on the heap. Because the generated MIR is hard
/// to translate, we provide a custom `vec!` macro which does not do this.
#[macro_export]
macro_rules! vec {
    () => (
        ::std::vec::Vec::new()
    );
    ($elem:expr; $n:expr) => (
        ::std::vec::from_elem($elem, $n)
    );
    ($($x:expr),*) => (
        <[_]>::into_vec(::std::boxed::Box::new([$($x),*]))
    );
    ($($x:expr,)*) => (vec![$($x),*])
}
pub use vec;
