use super::Iterator;
use crate as creusot_contracts;
use crate::{
    logic::{Int, Seq},
    std::ops::*,
    Ghost, Invariant,
};
use creusot_contracts_proc::*;

pub struct MapInv<I, A, F> {
    iter: I,
    func: F,
    produced: Ghost<Seq<A>>,
}

pub trait IteratorExt: Iterator + Sized {
    fn map_inv<B, F: FnMut(Self::Item, Ghost<Seq<Self::Item>>) -> B>(
        self,
        func: F,
    ) -> MapInv<Self, Self::Item, F>;
}

impl<I: Iterator> IteratorExt for I {
    #[requires(forall<e : Self::Item, i2 : Self> i2.invariant() ==> self.produces(Seq::singleton(e), i2) ==> func.precondition((e, Ghost::new(Seq::EMPTY))))]
    #[requires(MapInv::<Self, _, F>::reinitialize())]
    #[requires(MapInv::<Self, Self::Item, F>::preservation(self))]
    #[requires(self.invariant())]
    #[ensures(result.invariant())]
    #[ensures(result == MapInv { iter: self, func, produced: Ghost::new(Seq::EMPTY) })]
    fn map_inv<B, F: FnMut(Self::Item, Ghost<Seq<Self::Item>>) -> B>(
        self,
        func: F,
    ) -> MapInv<Self, Self::Item, F> {
        MapInv { iter: self, func, produced: ghost! {Seq::EMPTY} }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Iterator
    for MapInv<I, I::Item, F>
{
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            *(^self).produced == Seq::EMPTY &&
            (exists<iter: &mut I> *iter == self.iter && ^iter == (^self).iter && iter.completed()) &&
            self.func == (^self).func
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

    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.produced.len() + visited.len() == succ.produced.len()
            && succ.produced.subsequence(0, self.produced.len()).ext_eq(*self.produced)
            && self.iter.produces(succ.produced.subsequence(self.produced.len(), succ.produced.len()), succ.iter )
            && exists<fs: Seq<&mut F>>
                fs.len() == visited.len()
                && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
                && if visited.len() == 0 { self.func == succ.func }
                   else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
                && forall<i : Int> 0 <= i && i < visited.len() ==>
                    fs[i].postcondition_mut((succ.produced[self.produced.len() + i], Ghost::new(succ.produced.subsequence(0, self.produced.len() + i))), visited[i])
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Invariant
    for MapInv<I, I::Item, F>
{
    // Should not quantify over self or the `invariant` cannot be made into a type invariant
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            self.preservation_inv() &&
            self.iter.invariant() &&
            self.next_precondition()
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> ::std::iter::Iterator
    for MapInv<I, I::Item, F>
{
    type Item = B;

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces_one(v, ^self)
    })]
    #[maintains((mut self).invariant())]
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                proof_assert! { self.func.precondition((v, self.produced)) };
                ghost! { Self::produces_one_invariant };
                let produced = ghost! { self.produced.push(v) };
                let r = Some((self.func)(v, ghost! { self.produced.inner() })); // FIXME: Ghost should be Copy
                self.produced = produced;
                r
            }
            None => {
                self.produced = ghost! { Seq::EMPTY };
                None
            }
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> MapInv<I, I::Item, F> {
    #[predicate]
    fn next_precondition(self) -> bool {
        pearlite! {
            forall<e: I::Item, i: I>
                i.invariant() ==>
                self.iter.produces(Seq::singleton(e), i) ==>
                self.func.precondition((e, self.produced))
        }
    }

    #[predicate]
    fn reinitialize() -> bool {
        pearlite! {
            forall<reset : &mut MapInv<I, _, F>>
                reset.completed() ==>
                (^reset).iter.invariant() ==>
                (^reset).next_precondition() &&
                Self::preservation((^reset).iter)
        }
    }

    #[predicate]
    #[ensures(self.produced.inner() == Seq::EMPTY ==> result == Self::preservation(self.iter))]
    fn preservation_inv(self) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                i.invariant() ==>
                self.iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Ghost::new(self.produced.concat(s)))) ==>
                f.postcondition_mut((e1, Ghost::new(self.produced.concat(s))), b) ==>
                (^f).precondition((e2, Ghost::new(self.produced.concat(s).push(e1))))
        }
    }

    #[predicate]
    fn preservation(iter: I) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                i.invariant() ==>
                iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Ghost::new(s))) ==>
                f.postcondition_mut((e1, Ghost::new(s)), b) ==>
                (^f).precondition((e2, Ghost::new(s.push(e1))))
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.produces_one(e, other))]
    #[requires(other.iter.invariant())]
    #[ensures(other.invariant())]
    fn produces_one_invariant(self, e: B, other: Self) {}

    #[predicate]
    #[ensures(result == self.produces(Seq::singleton(visited), succ))]
    fn produces_one(self, visited: B, succ: Self) -> bool {
        pearlite! {
            exists<f: &mut F> *f == self.func && ^f == succ.func
            && { let e = succ.produced[self.produced.len()];
                 succ.produced.inner() == self.produced.push(e)
                 && self.iter.produces(Seq::singleton(e), succ.iter)
                 && f.postcondition_mut((e, self.produced), visited) }
        }
    }
}
