use crate::{std::iter::Zip, *};

pub trait ZipExt<A: Iterator, B: Iterator> {
    #[ghost]
    fn itera(self) -> A;

    #[ghost]
    fn iterb(self) -> B;
}

impl<A: Iterator, B: Iterator> ZipExt<A, B> for Zip<A, B> {
    #[ghost]
    #[open(self)]
    #[trusted]
    fn itera(self) -> A {
        pearlite! { absurd }
    }

    #[ghost]
    #[open(self)]
    #[trusted]
    fn iterb(self) -> B {
        pearlite! { absurd }
    }
}

impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    #[open]
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<a: &mut A, b: &mut B>
                   *a == (*self).itera() && *b == (*self).iterb()
                && ^a == (^self).itera() && ^b == (^self).iterb()
                && (a.completed() && b.resolve()
                    || exists<x: A::Item> a.produces(Seq::singleton(x), ^a) &&
                                          x.resolve() && b.completed())
        }
    }

    #[open]
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            // Using an `unzip` definition doesn't work well because of issues related to datatypes and `match`
            exists<p1 : Seq<_>, p2 : Seq<_>>
                p1.len() == p2.len() && p2.len() == visited.len() &&
                (forall<i :_> 0 <= i && i < visited.len() ==> visited[i] == (p1[i], p2[i])) &&
                self.itera().produces(p1, o.itera()) && self.iterb().produces(p2, o.iterb())
        }
    }

    #[law]
    #[open(self)]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[open(self)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
