#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{prelude::*, std::iter::DoubleEndedIteratorSpec};
use core::iter::Chain;

pub trait ChainExt<A, B> {
    #[logic]
    fn iter_a(self) -> Option<A>;

    #[logic]
    fn iter_b(self) -> Option<B>;
}

impl<A, B> ChainExt<A, B> for Chain<A, B> {
    #[logic(opaque)]
    fn iter_a(self) -> Option<A> {
        dead
    }

    #[logic(opaque)]
    fn iter_b(self) -> Option<B> {
        dead
    }
}

impl<A, B> Resolve for Chain<A, B> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        resolve(self.iter_a()) && resolve(self.iter_b())
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<A, B> Invariant for Chain<A, B> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        inv(self.iter_a()) && inv(self.iter_b())
    }
}

impl<A: IteratorSpec, B: IteratorSpec<Item = A::Item>> IteratorSpec for Chain<A, B> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (match self.iter_a() {
                None => true,
                Some(sa) => exists<a: &mut A> sa == *a && a.completed() && resolve(^a)
            }) &&
            (^self).iter_a() == None &&
            (match self.iter_b() {
                None => true,
                Some(sb) => exists<b: &mut B> sb == *b && b.completed() && (^self).iter_b() == Some(^b)
            })
        }
    }

    #[logic(open, prophetic, inline)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<visited_a: Seq<A::Item>, visited_b: Seq<B::Item>>
                visited == visited_a.concat(visited_b) &&
                chain_produces_inner(self, visited_a, visited_b, o)
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law, prophetic)]
    #[requires(x.produces(xy, y))]
    #[requires(y.produces(yz, z))]
    #[ensures(x.produces(xy.concat(yz), z))]
    fn produces_trans(x: Self, xy: Seq<Self::Item>, y: Self, yz: Seq<Self::Item>, z: Self) {
        let _ = chain_produces_inner_trans::<A, B>;
    }
}

extern_spec! {
    impl<A: Iterator, B: Iterator<Item = A::Item>> Chain<A, B> {
        #[ensures(exists<sa, sb>
            match self.iter_a() {
                Some(a) => A::size_hint.postcondition((&a,), sa),
                None => sa == (0usize, Some(0usize)),
            } &&
            match self.iter_b() {
                Some(b) => B::size_hint.postcondition((&b,), sb),
                None => sb == (0usize, Some(0usize)),
            } &&
            result.0 == if sa.0@ + sb.0@ > usize::MAX@ { usize::MAX } else { sa.0 + sb.0 } &&
            result.1 == match (sa.1, sb.1) {
                (Some(x), Some(y)) => if x@ + y@ > usize::MAX@ { None } else { Some(x + y) },
                _ =>  None,
            }
        )]
        fn size_hint(&self) -> (usize, Option<usize>);
    }
}

impl<A: DoubleEndedIteratorSpec, B: DoubleEndedIteratorSpec<Item = A::Item>> DoubleEndedIteratorSpec
    for Chain<A, B>
{
    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        pearlite! {
            (match self.iter_b() {
                None => true,
                Some(sb) => exists<b: &mut B> sb == *b && b.completed_back() && resolve(^b)
            }) &&
            (^self).iter_b() == None &&
            (match self.iter_a() {
                None => true,
                Some(sa) => exists<a: &mut A> sa == *a && a.completed_back() && (^self).iter_a() == Some(^a)
            })
        }
    }

    #[logic(open, prophetic, inline)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<visited_a: Seq<A::Item>, visited_b: Seq<B::Item>>
                visited == visited_b.concat(visited_a) &&
                chain_produces_inner_back(self, visited_a, visited_b, o)
        }
    }

    #[logic(law)]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self) {}

    #[logic(law, prophetic)]
    #[requires(x.produces_back(xy, y))]
    #[requires(y.produces_back(yz, z))]
    #[ensures(x.produces_back(xy.concat(yz), z))]
    fn produces_back_trans(x: Self, xy: Seq<Self::Item>, y: Self, yz: Seq<Self::Item>, z: Self) {
        let _ = chain_produces_inner_back_trans::<A, B>;
    }

    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces_back(s, *i) && i.completed_back() ==> r.0@ <= s.len())]
    #[ensures(match r.1 {
        Some(r) => {
            forall<s: Seq<Self::Item>, i: Self> self.produces_back(s, i) ==> s.len() <= r@
        }
        None => true
    })]
    fn size_hint_back_spec(&self, r: (usize, Option<usize>)) {}
}

#[logic(open, prophetic)]
pub fn chain_produces_inner<A: IteratorSpec, B: IteratorSpec<Item = A::Item>>(
    x: Chain<A, B>,
    visited_a: Seq<A::Item>,
    visited_b: Seq<B::Item>,
    y: Chain<A, B>,
) -> bool {
    pearlite! {
        (match x.iter_a() {
            None => y.iter_a() == None && visited_a == Seq::empty(),
            Some(xa) => match y.iter_a() {
                None => exists<ya: &mut A> xa.produces(visited_a, *ya) && ya.completed() && resolve(^ya),
                Some(ya) => xa.produces(visited_a, ya)
            }
        })
        &&
        (match y.iter_a() {
            Some(_) => x.iter_b() == y.iter_b() && visited_b == Seq::empty(),
            None => match (x.iter_b(), y.iter_b()) {
                (None, _) => y.iter_b() == None && visited_b == Seq::empty(),
                (Some(sb), Some(yb)) => sb.produces(visited_b, yb),
                (Some(_), None) => false
            }
        })
    }
}

#[logic]
#[requires(chain_produces_inner(x, visited_a_xy, visited_b_xy, y))]
#[requires(chain_produces_inner(y, visited_a_yz, visited_b_yz, z))]
#[ensures(#[trigger(chain_produces_inner(x, visited_a_xy, visited_b_xy, y), chain_produces_inner(y, visited_a_yz, visited_b_yz, z))]
    chain_produces_inner(x, visited_a_xy.concat(visited_a_yz), visited_b_xy.concat(visited_b_yz), z))]
fn chain_produces_inner_trans<A: IteratorSpec, B: IteratorSpec<Item = A::Item>>(
    x: Chain<A, B>,
    visited_a_xy: Seq<A::Item>,
    visited_b_xy: Seq<B::Item>,
    y: Chain<A, B>,
    visited_a_yz: Seq<A::Item>,
    visited_b_yz: Seq<B::Item>,
    z: Chain<A, B>,
) {
    proof_assert!(
        Seq::<A::Item>::empty().concat(Seq::<A::Item>::empty()) == Seq::<A::Item>::empty()
    );
}

#[logic(open, prophetic)]
pub fn chain_produces_inner_back<
    A: DoubleEndedIteratorSpec,
    B: DoubleEndedIteratorSpec<Item = A::Item>,
>(
    x: Chain<A, B>,
    visited_a: Seq<A::Item>,
    visited_b: Seq<B::Item>,
    y: Chain<A, B>,
) -> bool {
    pearlite! {
        (match x.iter_b() {
            None => y.iter_b() == None && visited_b == Seq::empty(),
            Some(xb) => match y.iter_b() {
                None => exists<yb: &mut B> xb.produces_back(visited_b, *yb) && yb.completed_back() && resolve(^yb),
                Some(yb) => xb.produces_back(visited_b, yb)
            }
        })
        &&
        (match y.iter_b() {
            Some(_) => x.iter_a() == y.iter_a() && visited_a == Seq::empty(),
            None => match (x.iter_a(), y.iter_a()) {
                (None, _) => y.iter_a() == None && visited_a == Seq::empty(),
                (Some(xa), Some(ya)) => xa.produces_back(visited_a, ya),
                (Some(_), None) => false
            }
        })
    }
}

#[logic]
#[requires(chain_produces_inner_back(x, visited_a_xy, visited_b_xy, y))]
#[requires(chain_produces_inner_back(y, visited_a_yz, visited_b_yz, z))]
#[ensures(#[trigger(chain_produces_inner_back(x, visited_a_xy, visited_b_xy, y), chain_produces_inner_back(y, visited_a_yz, visited_b_yz, z))]
    chain_produces_inner_back(x, visited_a_xy.concat(visited_a_yz), visited_b_xy.concat(visited_b_yz), z))]
fn chain_produces_inner_back_trans<
    A: DoubleEndedIteratorSpec,
    B: DoubleEndedIteratorSpec<Item = A::Item>,
>(
    x: Chain<A, B>,
    visited_a_xy: Seq<A::Item>,
    visited_b_xy: Seq<B::Item>,
    y: Chain<A, B>,
    visited_a_yz: Seq<A::Item>,
    visited_b_yz: Seq<B::Item>,
    z: Chain<A, B>,
) {
    proof_assert!(
        Seq::<A::Item>::empty().concat(Seq::<A::Item>::empty()) == Seq::<A::Item>::empty()
    );
}
