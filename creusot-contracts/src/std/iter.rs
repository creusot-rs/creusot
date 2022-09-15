use crate as creusot_contracts;
use crate::Seq;
use creusot_contracts_proc::*;

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
