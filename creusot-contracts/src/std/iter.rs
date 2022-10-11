use crate as creusot_contracts;
use crate::{logic::Seq, resolve::Resolve, Invariant};
use creusot_contracts_proc::*;
use std::iter::{Skip, Take};

mod map_inv;
pub use map_inv::{IteratorExt, MapInv};

mod skip;
pub use skip::SkipExt;

mod take;
pub use take::TakeExt;

mod range;

pub trait Iterator: std::iter::Iterator + Invariant {
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, _: Self) -> bool;

    #[predicate]
    fn completed(&mut self) -> bool;

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self);

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);
}

pub trait FromIterator<A>: std::iter::FromIterator<A> {
    #[predicate]
    fn from_iter_logic(prod: Seq<A>, res: Self) -> bool;
}

extern_spec! {
    mod std {
        mod iter {
            trait Iterator
                where Self : Iterator + Invariant {

                #[requires((*self).invariant())]
                #[ensures((^self).invariant())]
                #[ensures(match result {
                    None => self.completed(),
                    Some(v) => (*self).produces(Seq::singleton(v), ^self)
                })]
                fn next(&mut self) -> Option<Self::Item>;

                #[requires(self.invariant())]
                #[ensures(result.invariant())]
                #[ensures(result.iter() == self && result.n() == @n)]
                fn skip(self, n: usize) -> Skip<Self>;

                #[requires(self.invariant())]
                #[ensures(result.invariant())]
                #[ensures(result.iter() == self && result.n() == @n)]
                fn take(self, n: usize) -> Take<Self>;

                #[ensures(exists<done_ : &mut Self_, prod: Seq<_>> (^done_).resolve() && done_.completed() &&
                    self.produces(prod, *done_) && B::from_iter_logic(prod, result))]
                fn collect<B>(self) -> B
                    where B : FromIterator<Self::Item>;
            }

            trait FromIterator<A>
                where Self: FromIterator<A> {

            // TODO: Investigate why Self_ needed
            #[ensures(Self_::from_iter_logic(Seq::EMPTY, result))]
            fn from_iter<T>(iter: T) -> Self
                where
                    T: IntoIterator<Item = A>;
            }
        }
    }
}

extern_spec! {
    impl<I : Iterator + Invariant> IntoIterator for I {
        #[ensures(result == self)]
        #[ensures(result.invariant())]
        fn into_iter(self) -> I;
    }
}
