use crate::{invariant::*, std::iter::Zip, *};

pub trait ZipExt<A: Iterator, B: Iterator> {
    #[logic]
    fn itera(self) -> A;

    #[logic]
    fn iterb(self) -> B;
}

impl<A: Iterator, B: Iterator> ZipExt<A, B> for Zip<A, B> {
    #[trusted]
    #[logic(opaque)]
    #[ensures(inv(self) ==> inv(result))]
    fn itera(self) -> A {
        dead
    }

    #[trusted]
    #[logic(opaque)]
    #[ensures(inv(self) ==> inv(result))]
    fn iterb(self) -> B {
        dead
    }
}

impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<a: &mut A, b: &mut B>
                   *a == (*self).itera() && *b == (*self).iterb()
                && ^a == (^self).itera() && ^b == (^self).iterb()
                && (a.completed() && resolve(b)
                    || exists<x: A::Item> inv(x) && (*a).produces(Seq::singleton(x), ^a) &&
                                          resolve(x) && (*b).completed())
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            // Using an `unzip` definition doesn't work well because of issues related to datatypes and `match`
            exists<p1: Seq<_>, p2: Seq<_>>
                   p1.len() == p2.len() && p2.len() == visited.len()
                && (forall<i> 0 <= i && i < visited.len() ==> visited[i] == (p1[i], p2[i]))
                && self.itera().produces(p1, o.itera()) && self.iterb().produces(p2, o.iterb())
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
