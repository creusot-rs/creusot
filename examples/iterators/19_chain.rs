// TIME 5

#![feature(try_blocks)]
extern crate creusot_std;
use creusot_std::prelude::*;

pub mod common;
use common::{DoubleEndedIterator, Iterator};

pub struct Chain<A, B> {
    pub a: Option<A>,
    pub b: Option<B>,
}

impl<A: Iterator, B: Iterator<Item = A::Item>> Iterator for Chain<A, B> {
    type Item = A::Item;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (match self.a {
                None => true,
                Some(sa) => exists<a: &mut A> sa == *a && a.completed() && resolve(^a)
            }) &&
            (^self).a == None &&
            (match self.b {
                None => true,
                Some(sb) => exists<b: &mut B> sb == *b && b.completed() && (^self).b == Some(^b)
            })
        }
    }

    #[logic(open, prophetic, inline)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<visited_a: Seq<A::Item>, visited_b: Seq<B::Item>>
                visited == visited_a.concat(visited_b) &&
                self.produces_inner(visited_a, visited_b, o)
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
        let _ = Self::produces_inner_trans;
    }

    #[ensures(match result {
        None => self.completed(),
        Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        try {
            let x = self.a.as_mut()?.next();
            if x.is_none() {
                self.a = None;
            }
            x?
        }
        .or_else(|| self.b.as_mut()?.next())
    }

    #[ensures(exists<sa, sb>
        match self.a {
            Some(a) => A::size_hint.postcondition((&a,), sa),
            None => sa == (0usize, Some(0usize)),
        } &&
        match self.b {
            Some(b) => B::size_hint.postcondition((&b,), sb),
            None => sb == (0usize, Some(0usize)),
        } &&
        result.0 == if sa.0@ + sb.0@ > usize::MAX@ { usize::MAX } else { sa.0 + sb.0 } &&
        result.1 == match (sa.1, sb.1) {
            (Some(x), Some(y)) => if x@ + y@ > usize::MAX@ { None } else { Some(x + y) },
            _ =>  None,
        }
    )]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Chain { a: Some(a), b: Some(b) } => {
                let (a_lower, a_upper) = a.size_hint();
                let (b_lower, b_upper) = b.size_hint();

                let lower = a_lower.saturating_add(b_lower);

                let upper = match (a_upper, b_upper) {
                    (Some(x), Some(y)) => x.checked_add(y),
                    _ => None,
                };

                (lower, upper)
            }
            Chain { a: Some(a), b: None } => a.size_hint(),
            Chain { a: None, b: Some(b) } => b.size_hint(),
            Chain { a: None, b: None } => (0, Some(0)),
        }
    }
}

impl<A: DoubleEndedIterator, B: DoubleEndedIterator<Item = A::Item>> DoubleEndedIterator
    for Chain<A, B>
{
    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        pearlite! {
            (match self.b {
                None => true,
                Some(sb) => exists<b: &mut B> sb == *b && b.completed_back() && resolve(^b)
            }) &&
            (^self).b == None &&
            (match self.a {
                None => true,
                Some(sa) => exists<a: &mut A> sa == *a && a.completed_back() && (^self).a == Some(^a)
            })
        }
    }

    #[logic(open, prophetic, inline)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<visited_a: Seq<A::Item>, visited_b: Seq<B::Item>>
                visited == visited_b.concat(visited_a) &&
                self.produces_inner_back(visited_a, visited_b, o)
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
        let _ = Self::produces_inner_back_trans;
    }

    #[ensures(match result {
        None => self.completed_back(),
        Some(v) => (*self).produces_back(Seq::singleton(v), ^self)
    })]
    fn next_back(&mut self) -> Option<Self::Item> {
        try {
            let x = self.b.as_mut()?.next_back();
            if x.is_none() {
                self.b = None;
            }
            x?
        }
        .or_else(|| self.a.as_mut()?.next_back())
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

impl<A: Iterator, B: Iterator<Item = A::Item>> Chain<A, B> {
    #[logic(open, prophetic)]
    pub fn produces_inner(self, visited_a: Seq<A::Item>, visited_b: Seq<B::Item>, o: Self) -> bool {
        pearlite! {
            (match self.a {
                None => o.a == None && visited_a == Seq::empty(),
                Some(sa) => match o.a {
                    None => exists<oa: &mut A> sa.produces(visited_a, *oa) && oa.completed() && resolve(^oa),
                    Some(oa) => sa.produces(visited_a, oa)
                }
            })
            &&
            (match o.a {
                Some(_) => self.b == o.b && visited_b == Seq::empty(),
                None => match (self.b, o.b) {
                    (None, _) => o.b == None && visited_b == Seq::empty(),
                    (Some(sb), Some(ob)) => sb.produces(visited_b, ob),
                    (Some(_), None) => false
                }
            })
        }
    }

    #[logic]
    #[requires(x.produces_inner(visited_a_xy, visited_b_xy, y))]
    #[requires(y.produces_inner(visited_a_yz, visited_b_yz, z))]
    #[ensures(#[trigger(x.produces_inner(visited_a_xy, visited_b_xy, y), y.produces_inner(visited_a_yz, visited_b_yz, z))]
        x.produces_inner(visited_a_xy.concat(visited_a_yz), visited_b_xy.concat(visited_b_yz), z))]
    fn produces_inner_trans(
        x: Self,
        visited_a_xy: Seq<A::Item>,
        visited_b_xy: Seq<B::Item>,
        y: Self,
        visited_a_yz: Seq<A::Item>,
        visited_b_yz: Seq<B::Item>,
        z: Self,
    ) {
        proof_assert!(
            Seq::<A::Item>::empty().concat(Seq::<A::Item>::empty()) == Seq::<A::Item>::empty()
        );
    }
}

impl<A: DoubleEndedIterator, B: DoubleEndedIterator<Item = A::Item>> Chain<A, B> {
    #[logic(open, prophetic)]
    pub fn produces_inner_back(
        self,
        visited_a: Seq<A::Item>,
        visited_b: Seq<B::Item>,
        o: Self,
    ) -> bool {
        pearlite! {
            (match self.b {
                None => o.b == None && visited_b == Seq::empty(),
                Some(sb) => match o.b {
                    None => exists<ob: &mut B> sb.produces_back(visited_b, *ob) && ob.completed_back() && resolve(^ob),
                    Some(ob) => sb.produces_back(visited_b, ob)
                }
            })
            &&
            (match o.b {
                Some(_) => self.a == o.a && visited_a == Seq::empty(),
                None => match (self.a, o.a) {
                    (None, _) => o.a == None && visited_a == Seq::empty(),
                    (Some(sa), Some(oa)) => sa.produces_back(visited_a, oa),
                    (Some(_), None) => false
                }
            })
        }
    }

    #[logic]
    #[requires(x.produces_inner_back(visited_a_xy, visited_b_xy, y))]
    #[requires(y.produces_inner_back(visited_a_yz, visited_b_yz, z))]
    #[ensures(#[trigger(x.produces_inner_back(visited_a_xy, visited_b_xy, y), y.produces_inner_back(visited_a_yz, visited_b_yz, z))]
        x.produces_inner_back(visited_a_xy.concat(visited_a_yz), visited_b_xy.concat(visited_b_yz), z))]
    fn produces_inner_back_trans(
        x: Self,
        visited_a_xy: Seq<A::Item>,
        visited_b_xy: Seq<B::Item>,
        y: Self,
        visited_a_yz: Seq<A::Item>,
        visited_b_yz: Seq<B::Item>,
        z: Self,
    ) {
        proof_assert!(
            Seq::<A::Item>::empty().concat(Seq::<A::Item>::empty()) == Seq::<A::Item>::empty()
        );
    }
}
