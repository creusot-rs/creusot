#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{std::*, *};

mod common;
use common::*;

pub struct Map<I, A, F> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,

    produced: Ghost<Seq<A>>,
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Iterator for Map<I, I::Item, F> {
    type Item = B;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            *(^self).produced == Seq::EMPTY &&
            (exists<iter: &mut I> *iter == self.iter && ^iter == (^self).iter && iter.completed())
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
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.produced.len() + visited.len() == succ.produced.len()
            && succ.produced.subsequence(0, self.produced.len()).ext_eq(*self.produced)
            && self.iter.produces(succ.produced.subsequence(self.produced.len(), succ.produced.len()), succ.iter )
            && exists<fs: Seq<&mut F>>
                fs.len() == visited.len()
                && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
                && (visited.len() > 0 ==>
                        * fs[0] == self.func
                    &&  ^ fs[visited.len() - 1] == succ.func)
                && (visited.len() == 0 ==> self.func == succ.func)
                && forall<i : Int> 0 <= i && i < visited.len() ==>
                    fs[i].postcondition_mut((succ.produced[self.produced.len() + i], Ghost(succ.produced.subsequence(0, self.produced.len() + i))), visited[i])
        }
    }

    // Should not quantify over self or the `invariant` cannot be made into a type invariant
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            self.preservation() &&
            self.iter.invariant() &&
            self.next_precondition()
        }
    }

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces_one(v, ^self)
    })]
    #[maintains((mut self).invariant())]
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                proof_assert! { self.func.precondition((v, self.produced)) };
                ghost! { Self::preservation_produces_one };
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

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Map<I, I::Item, F> {
    // Probably needs to be reworked
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
            forall<reset : &mut Map<I, _, F>>
                reset.completed() ==>
                (^reset).iter.invariant() ==>
                (^reset).next_precondition() &&
                (^reset).preservation()
        }
    }

    #[predicate]
    fn preservation(self) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                i.invariant() ==>
                self.iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Ghost(self.produced.concat(s)))) ==>
                f.postcondition_mut((e1, Ghost(self.produced.concat(s))), b) ==>
                (^f).precondition((e2, Ghost(self.produced.concat(s).push(e1))))
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.produces_one(e, other))]
    #[requires(other.iter.invariant())]
    #[ensures(other.invariant())]
    fn preservation_produces_one(self, e: B, other: Self) {}

    #[predicate]
    #[ensures(result == self.produces(Seq::singleton(visited), succ))]
    fn produces_one(self, visited: B, succ: Self) -> bool {
        pearlite! {
            exists<f: &mut F> * f == self.func &&  ^ f == succ.func
            && { let e = succ.produced[self.produced.len()];
                 succ.produced.inner() == self.produced.push(e)
                 && self.iter.produces(Seq::singleton(e), succ.iter)
                 && f.postcondition_mut((e, self.produced), visited) }
        }
    }
}

#[requires(forall<e : I::Item, i2 : I> i2.invariant() ==> iter.produces(Seq::singleton(e), i2) ==> func.precondition((e, Ghost(Seq::EMPTY))))]
#[requires(Map::<I, _, F>::reinitialize())]
#[requires(iter.invariant())]
#[requires(
    forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
        i.invariant() ==>
        iter.produces(s.push(e1).push(e2), i) ==>
        (*f).precondition((e1, Ghost(s))) ==>
        f.postcondition_mut((e1, Ghost(s)), b) ==>
        (^f).precondition((e2, Ghost(s.push(e1))))
)]
#[ensures(result.invariant())]
#[ensures(result == Map { iter, func, produced: Ghost(Seq::EMPTY) })]
pub fn map<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B>(
    iter: I,
    func: F,
) -> Map<I, I::Item, F> {
    Map { iter, func, produced: ghost! {Seq::EMPTY} }
}

#[requires(iter.invariant())]
pub fn identity<I: Iterator>(iter: I) {
    map(iter, |x, _| x);
}

#[requires(iter.invariant())]
#[requires(forall<done_ : &mut I> done_.completed() ==> (^done_).invariant() ==> forall<next : I, steps: Seq<_>> (^done_).produces(steps, next) ==> steps == Seq::EMPTY && ^done_ == next)]
#[requires(forall<prod : _, fin: I> fin.invariant() ==> iter.produces(prod, fin) ==>
    forall<x : _> 0 <= x && x < prod.len() ==> prod[x] <= 10u32
)]
#[requires(forall<prod : _, fin: I> fin.invariant() ==> iter.produces(prod, fin) ==>
    forall<x : _> 0 <= x && x < prod.len() ==> prod[x] <= 10u32
)]
pub fn increment<I: Iterator<Item = u32>>(iter: I) {
    let i = map(
        iter,
        #[requires(@x <= 15)]
        #[ensures(@result == @x+1)]
        |x: u32, _| x + 1,
    );

    proof_assert! {
        forall<prod : _, fin: Map<_, _, _>> fin.invariant() ==> i.produces(prod, fin) ==>
            forall<x : _> 0 <= x && x < prod.len() ==> prod[x] <= 11u32
    };
}

#[requires(iter.invariant())]
#[requires(forall<done_ : &mut I> done_.completed() ==> (^done_).invariant() ==> forall<next : I, steps: Seq<_>> (^done_).produces(steps, next) ==> steps == Seq::EMPTY && ^done_ == next)]
#[requires(forall<prod : _, fin: I> fin.invariant() ==> iter.produces(prod, fin) ==> prod.len() <= @usize::MAX)]
pub fn counter<I: Iterator<Item = u32>>(iter: I) {
    let mut cnt = 0;
    map(
        iter,
        #[requires(@cnt == (*_prod).len() && cnt < usize::MAX)]
        #[ensures(@cnt == @old(cnt) + 1 && @cnt == (*_prod).len() + 1)]
        |x, _prod: Ghost<Seq<_>>| {
            cnt += 1;
            x
        },
    );
}
