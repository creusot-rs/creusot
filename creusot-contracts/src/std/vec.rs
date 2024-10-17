use crate::{
    invariant::*,
    resolve::structural_resolve,
    std::{
        alloc::Allocator,
        ops::{Deref, DerefMut, Index, IndexMut},
        slice::SliceIndex,
    },
    Default, *,
};
pub use ::std::vec::*;

impl<T, A: Allocator> View for Vec<T, A> {
    type ViewTy = Seq<T>;

    #[open(self)]
    #[logic]
    #[trusted]
    #[ensures(result.len() <= usize::MAX@)]
    fn view(self) -> Seq<T> {
        pearlite! { absurd }
    }
}

impl<T: DeepModel, A: Allocator> DeepModel for Vec<T, A> {
    type DeepModelTy = Seq<T::DeepModelTy>;

    #[logic]
    #[open(self)]
    #[trusted]
    #[ensures(self.view().len() == result.len())]
    #[ensures(forall<i: Int> 0 <= i && i < self.view().len()
              ==> result[i] == self[i].deep_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { absurd }
    }
}

impl<T> Default for Vec<T> {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        pearlite! { self.view().len() == 0 }
    }
}

impl<T, A: Allocator> Resolve for Vec<T, A> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! { forall<i : Int> 0 <= i && i < self@.len() ==> resolve(&self[i]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<T, A: Allocator> Invariant for Vec<T, A> {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { invariant::inv(self@) }
    }
}

extern_spec! {
    mod std {
        mod vec {
            impl<T> Vec<T> {
                #[pure]
                #[ensures(result@.len() == 0)]
                fn new() -> Vec<T>;

                #[terminates] // can OOM
                #[ensures(result@.len() == 0)]
                fn with_capacity(capacity: usize) -> Vec<T>;
            }
            impl<T, A : Allocator> Vec<T, A> {
                #[pure]
                #[ensures(result@ == self@.len())]
                fn len(&self) -> usize;

                #[terminates] // can OOM
                #[ensures((^self)@ == self@.push(v))]
                fn push(&mut self, v: T);

                #[pure]
                #[ensures(match result {
                    Some(t) =>
                        (^self)@ == self@.subsequence(0, self@.len() - 1) &&
                        self@ == (^self)@.push(t),
                    None => *self == ^self && self@.len() == 0
                })]
                fn pop(&mut self) -> Option<T>;

                #[pure]
                #[requires(ix@ < self@.len())]
                #[ensures(result == self[ix@])]
                #[ensures((^self)@ == self@.subsequence(0, ix@).concat(self@.subsequence(ix@ + 1, self@.len())))]
                #[ensures((^self)@.len() == self@.len() - 1)]
                fn remove(&mut self, ix: usize) -> T;

                #[terminates] // can OOM
                #[ensures((^self)@.len() == self@.len() + 1)]
                #[ensures(forall<i: Int> 0 <= i && i < index@ ==> (^self)[i] == self[i])]
                #[ensures((^self)[index@] == element)]
                #[ensures(forall<i: Int> index@ < i && i < (^self)@.len() ==> (^self)[i] == self[i - 1])]
                fn insert(&mut self, index: usize, element: T);

                #[pure]
                #[ensures(result@ >= self@.len())]
                fn capacity(&self) -> usize;

                #[terminates] // can OOM
                #[ensures((^self)@ == self@)]
                fn reserve(&mut self, additional: usize);

                #[terminates] // can OOM
                #[ensures((^self)@ == self@)]
                fn reserve_exact(&mut self, additional: usize);

                #[pure]
                #[ensures((^self)@ == self@)]
                fn shrink_to_fit(&mut self);

                #[pure]
                #[ensures((^self)@ == self@)]
                fn shrink_to(&mut self, min_capacity: usize);

                #[pure]
                #[ensures((^self)@.len() == 0)]
                fn clear(&mut self);
            }

            impl<T, A : Allocator> Extend<T> for Vec<T, A> {
                #[requires(iter.into_iter_pre())]
                #[ensures(exists<start_ : I::IntoIter, done : &mut I::IntoIter, prod: Seq<T>>
                    inv(start_) && inv(done) && inv(prod) &&
                    iter.into_iter_post(start_) &&
                    done.completed() && start_.produces(prod, *done) && (^self)@ == self@.concat(prod)
                )]
                fn extend<I>(&mut self, iter: I)
                where
                    I : IntoIterator<Item = T>, I::IntoIter : Iterator;
            }

            impl<T, I : SliceIndex<[T]>, A : Allocator> IndexMut<I> for Vec<T, A> {
                #[pure]
                #[requires(ix.in_bounds(self@))]
                #[ensures(ix.has_value(self@, *result))]
                #[ensures(ix.has_value((^self)@, ^result))]
                #[ensures(ix.resolve_elswhere(self@, (^self)@))]
                #[ensures((^self)@.len() == self@.len())]
                fn index_mut(&mut self, ix: I) -> &mut <Vec<T, A> as Index<I>>::Output;
            }

            impl<T, I : SliceIndex<[T]>, A : Allocator> Index<I> for Vec<T, A> {
                #[pure]
                #[requires(ix.in_bounds(self@))]
                #[ensures(ix.has_value(self@, *result))]
                fn index(&self, ix: I) -> & <Vec<T, A> as Index<I>>::Output;
            }

            impl<T, A : Allocator> Deref for Vec<T, A> {
                #[pure]
                #[ensures(result@ == self@)]
                fn deref(&self) -> &[T];
            }

            impl<T, A : Allocator> DerefMut for Vec<T, A> {
                #[pure]
                #[ensures(result@ == self@)]
                #[ensures((^result)@ == (^self)@)]
                fn deref_mut(&mut self) -> &mut [T];
            }

            #[ensures(result@.len() == n@)]
            #[ensures(forall<i : Int> 0 <= i && i < n@ ==> result[i] == elem)]
            fn from_elem<T : Clone>(elem : T, n : usize) -> Vec<T>;
        }
    }
}

impl<T, A: Allocator> IntoIterator for Vec<T, A> {
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

impl<T, A: Allocator> IntoIterator for &Vec<T, A> {
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

impl<T, A: Allocator> IntoIterator for &mut Vec<T, A> {
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

impl<T, A: Allocator> View for std::vec::IntoIter<T, A> {
    type ViewTy = Seq<T>;

    #[open(self)]
    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        absurd
    }
}

impl<T, A: Allocator> Resolve for std::vec::IntoIter<T, A> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! { forall<i: Int> 0 <= i && i < self@.len() ==> resolve(&self@[i]) }
    }

    #[trusted]
    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<T, A: Allocator> Iterator for std::vec::IntoIter<T, A> {
    #[predicate(prophetic)]
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
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<T>, b: Self, bc: Seq<T>, c: Self) {}
}

impl<T> FromIterator<T> for Vec<T> {
    #[predicate]
    #[open]
    fn from_iter_post(prod: Seq<T>, res: Self) -> bool {
        pearlite! { prod == res@ }
    }
}
