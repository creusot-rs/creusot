use crate::{invariant::*, prelude::*, std::iter::ExactSizeIteratorSpec};
use core::iter::Zip;

pub trait ZipExt<A: Iterator, B: Iterator> {
    #[logic]
    fn iter_a(self) -> A;

    #[logic]
    fn iter_b(self) -> B;
}

impl<A: Iterator, B: Iterator> ZipExt<A, B> for Zip<A, B> {
    #[logic(opaque)]
    fn iter_a(self) -> A {
        dead
    }

    #[logic(opaque)]
    fn iter_b(self) -> B {
        dead
    }
}

impl<A: Iterator, B: Iterator> Invariant for Zip<A, B> {
    #[logic(prophetic, open, inline)]
    fn invariant(self) -> bool {
        inv(self.iter_a()) && inv(self.iter_b())
    }
}

impl<A: IteratorSpec, B: IteratorSpec> IteratorSpec for Zip<A, B> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<a: &mut A, b: &mut B>
                   *a == (*self).iter_a() && *b == (*self).iter_b()
                && ^a == (^self).iter_a() && ^b == (^self).iter_b()
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
                && self.iter_a().produces(p1, o.iter_a()) && self.iter_b().produces(p2, o.iter_b())
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

extern_spec! {
    impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
        #[ensures(exists<ra, rb>
            A::size_hint.postcondition((&self.iter_a(),), ra) &&
            B::size_hint.postcondition((&self.iter_b(),), rb) &&
            (ra.0@ <= rb.0@ ==> result.0 == ra.0) &&
            (ra.0@ >= rb.0@ ==> result.0 == rb.0) &&
            match (ra.1, rb.1) {
                (Some(ua), Some(ub)) =>
                    (ua@ <= ub@ ==> result.1 == Some(ua)) &&
                    (ua@ >= ub@ ==> result.1 == Some(ub)),
                (Some(ua), None) => result.1 == Some(ua),
                (None, Some(ub)) => result.1 == Some(ub),
                (None, None) => result.1 == None
            }
        )]
        fn size_hint(&self) -> (usize, Option<usize>);
    }
}

impl<A: ExactSizeIteratorSpec, B: ExactSizeIteratorSpec> ExactSizeIteratorSpec for Zip<A, B> {
    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {
        let _ = A::size_hint_exact;
        let _ = B::size_hint_exact;
    }
}
