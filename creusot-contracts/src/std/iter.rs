use crate as creusot_contracts;
use crate::{Int, Model, OrdLogic, Seq};
use creusot_contracts_proc::*;
use std::iter::Skip;

pub trait IteratorSpec: Iterator {
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
                where Self : IteratorSpec {

                #[ensures(match result {
                    None => self.completed(),
                    Some(v) => (*self).produces(Seq::singleton(v), ^self)
                })]
                fn next(&mut self) -> Option<Self_::Item>;

                #[ensures(@result == (self, @n))]
                fn skip(self, n: usize) -> Skip<Self_>;
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

impl<I> Model for Skip<I> {
    type ModelTy = (I, Int);

    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}

impl<I: IteratorSpec> IteratorSpec for Skip<I> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            (@^self).1 == 0 &&
            exists<s: Seq<Self::Item>, i: &mut I>
                s.len() <= (@*self).1 &&
                (@self).0.produces(s, *i) &&
                i.completed() &&
                ^i == (@^self).0
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            (@o).1 == 0 &&
            exists<s: Seq<Self::Item>>
                s.len() == (@self).1 &&
                (@self).0.produces(s.concat(visited), (@o).0) &&
                (s.len() < (@self).1 ==> visited == Seq::EMPTY)
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
