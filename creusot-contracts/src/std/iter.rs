use crate as creusot_contracts;
use crate::{
    logic::{Int, Seq},
    Invariant, Resolve,
};
use creusot_contracts_proc::*;
use std::iter::{FromIterator, Skip, Take};

mod map_inv;
pub use map_inv::{IteratorExt, MapInv};

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

pub trait FromIteratorSpec<A>: std::iter::FromIterator<A> {
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
                    where B : FromIteratorSpec<Self::Item>;
            }

            trait FromIterator<A>
                where Self: FromIteratorSpec<A> {

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

trait SkipExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> Int;
}

impl<I> SkipExt<I> for Skip<I> {
    #[logic]
    #[trusted]
    fn iter(self) -> I {
        pearlite! { absurd }
    }

    #[logic]
    #[trusted]
    #[ensures(result >= 0 && result <= @usize::MAX)]
    fn n(self) -> Int {
        pearlite! { absurd }
    }
}

impl<I: Invariant> Invariant for Skip<I> {
    #[predicate]
    fn invariant(self) -> bool {
        self.iter().invariant()
    }
}

impl<I: Iterator> Iterator for Skip<I> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            (^self).n() == 0 &&
            exists<s: Seq<Self::Item>, i: &mut I>
                s.len() <= (*self).n() &&
                self.iter().produces(s, *i) &&
                i.completed() &&
                ^i == (^self).iter()
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            o.n() == 0 &&
            exists<s: Seq<Self::Item>>
                s.len() == self.n() &&
                self.iter().produces(s.concat(visited), o.iter())
        }
    }

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

trait TakeExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> Int;
}

impl<I> TakeExt<I> for Take<I> {
    #[logic]
    #[trusted]
    fn iter(self) -> I {
        pearlite! { absurd }
    }

    #[logic]
    #[trusted]
    #[ensures(result >= 0 && result <= @usize::MAX)]
    fn n(self) -> Int {
        pearlite! { absurd }
    }
}

impl<I: Invariant> Invariant for Take<I> {
    #[predicate]
    fn invariant(self) -> bool {
        self.iter().invariant()
    }
}

impl<I: Iterator> Iterator for Take<I> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.n() == 0 && self.resolve() ||
            (*self).n() > 0 && (*self).n() == (^self).n() + 1 &&
                // Fixme: remove this existential quantification
                exists<i: &mut I> *i == (*self).iter() && ^i == (^self).iter() && i.completed()
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.n() == o.n() + visited.len() && self.iter().produces(visited, o.iter())
        }
    }

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
