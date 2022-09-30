use crate as creusot_contracts;
use crate::{Int, Resolve, Seq};
use creusot_contracts_proc::*;
use std::iter::{Skip, Take};

pub trait Iterator: std::iter::Iterator {
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, _: Self) -> bool;

    #[predicate]
    fn completed(&mut self) -> bool;

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self);

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);
}

extern_spec! {
    mod std {
        mod iter {
            trait Iterator
                where Self : Iterator {

                #[ensures(match result {
                    None => self.completed(),
                    Some(v) => (*self).produces(Seq::singleton(v), ^self)
                })]
                fn next(&mut self) -> Option<Self::Item>;

                #[ensures(result.iter() == self && result.n() == @n)]
                fn skip(self, n: usize) -> Skip<Self>;

                #[ensures(result.iter() == self && result.n() == @n)]
                fn take(self, n: usize) -> Take<Self>;
            }
        }
    }
}

extern_spec! {
    impl<I : Iterator> IntoIterator for I {
        #[ensures(result == self)]
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
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
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
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
