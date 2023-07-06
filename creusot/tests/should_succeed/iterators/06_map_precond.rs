#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{
    invariant::{inv, Invariant},
    *,
};

mod common;
use common::Iterator;

// FIXME: make it Map<I, A, F> again
pub struct Map<A, I: Iterator<Item = A>, B, F: FnMut(I::Item, Ghost<Seq<A>>) -> B> {
    iter: I,
    #[creusot::open_inv]
    func: F,
    #[creusot::open_inv]
    produced: Ghost<Seq<A>>,
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Iterator
    for Map<I::Item, I, B, F>
{
    type Item = B;

    #[open]
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            *(^self).produced == Seq::EMPTY &&
            self.iter.completed() && self.func == (^self).func
        }
    }

    #[law]
    #[open]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func.unnest(succ.func)
            && exists<s : Seq<I::Item>> s.len() == visited.len() && self.iter.produces(s, succ.iter)
            && succ.produced.inner() == self.produced.concat(s)
            && exists<fs: Seq<&mut F>> fs.len() == visited.len()
            && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
            && if visited.len() == 0 { self.func == succ.func }
               else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
            && forall<i : Int> 0 <= i && i < visited.len() ==>
                 self.func.unnest(*fs[i])
                 && (*fs[i]).precondition((s[i], Ghost::new(self.produced.concat(s.subsequence(0, i)))))
                 && fs[i].postcondition_mut((s[i], Ghost::new(self.produced.concat(s.subsequence(0, i)))), visited[i])
        }
    }

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces_one(v, ^self)
    })]
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

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Map<I::Item, I, B, F> {
    #[predicate]
    fn next_precondition(#[creusot::open_inv] self) -> bool {
        pearlite! {
            forall<e: I::Item, i: I>
                self.iter.produces(Seq::singleton(e), i) ==>
                self.func.precondition((e, self.produced))
        }
    }

    #[predicate]
    #[creusot::open_inv]
    fn reinitialize() -> bool {
        pearlite! {
            forall<reset : &mut Map<I::Item, I, B, F>>
                inv((*reset).iter) ==>
                reset.completed() ==>
                inv((^reset).iter) ==>
                (^reset).next_precondition() &&
                Self::preservation((^reset).iter, (^reset).func)
        }
    }

    #[predicate]
    #[ensures(self.produced.inner() == Seq::EMPTY ==> result == Self::preservation(self.iter, self.func))]
    fn preservation_inv(#[creusot::open_inv] self) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                self.func.unnest(*f) ==>
                self.iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Ghost::new(self.produced.concat(s)))) ==>
                f.postcondition_mut((e1, Ghost::new(self.produced.concat(s))), b) ==>
                (^f).precondition((e2, Ghost::new(self.produced.concat(s).push(e1))))
        }
    }

    #[predicate]
    fn preservation(iter: I, func: F) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                func.unnest(*f) ==>
                iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Ghost::new(s))) ==>
                f.postcondition_mut((e1, Ghost::new(s)), b) ==>
                (^f).precondition((e2, Ghost::new(s.push(e1))))
        }
    }

    #[logic]
    #[requires(self.produces_one(e, other))]
    #[requires(inv(other.iter))]
    #[ensures(inv(other))]
    fn produces_one_invariant(self, e: B, #[creusot::open_inv] other: Self) {}

    #[predicate]
    #[ensures(result == self.produces(Seq::singleton(visited), succ))]
    fn produces_one(
        #[creusot::open_inv] self,
        visited: B,
        #[creusot::open_inv] succ: Self,
    ) -> bool {
        pearlite! {
            exists<f: &mut F> *f == self.func && ^f == succ.func
            && { exists<e: I::Item> self.iter.produces(Seq::singleton(e), succ.iter)
                 && succ.produced.inner() == self.produced.push(e)
                 && (*f).precondition((e, self.produced))
                 && f.postcondition_mut((e, self.produced), visited) }
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Invariant
    for Map<I::Item, I, B, F>
{
    // Should not quantify over self or the `invariant` cannot be made into a type invariant
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            self.preservation_inv() &&
            self.next_precondition()
        }
    }
}

#[requires(forall<e : I::Item, i2 : I> iter.produces(Seq::singleton(e), i2) ==> func.precondition((e, Ghost::new(Seq::EMPTY))))]
#[requires(Map::<I::Item, I, B, F>::reinitialize())]
#[requires(Map::<I::Item, I, B, F>::preservation(iter, func))]
#[ensures(result == Map { iter, func, produced: Ghost::new(Seq::EMPTY) })]
pub fn map<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B>(
    iter: I,
    func: F,
) -> Map<I::Item, I, B, F> {
    Map { iter, func, produced: ghost! {Seq::EMPTY} }
}

pub fn identity<I: Iterator>(iter: I) {
    map(iter, |x, _| x);
}

#[requires(forall<done_ : &mut I> done_.completed() ==> inv(^done_) ==> forall<next : I, steps: Seq<_>> (^done_).produces(steps, next) ==> steps == Seq::EMPTY && ^done_ == next)]
#[requires(forall<prod : _, fin: I> iter.produces(prod, fin) ==>
    forall<x : _> 0 <= x && x < prod.len() ==> prod[x] <= 10u32
)]
pub fn increment<I: Iterator<Item = u32>>(iter: I) {
    let i = map(
        iter,
        #[requires(x@ <= 15)]
        #[ensures(result@ == x@+1)]
        |x: u32, _| x + 1,
    );

    proof_assert! {
        forall<prod : _, fin: Map<_, _, _, _>> i.produces(prod, fin) ==>
            forall<x : _> 0 <= x && x < prod.len() ==> prod[x] <= 11u32
    };
}

#[requires(forall<done_ : &mut I> done_.completed() ==> inv(^done_) ==> forall<next : I, steps: Seq<_>> (^done_).produces(steps, next) ==> steps == Seq::EMPTY && ^done_ == next)]
#[requires(forall<prod : _, fin: I> iter.produces(prod, fin) ==> prod.len() <= usize::MAX@)]
pub fn counter<I: Iterator<Item = u32>>(iter: I) {
    let mut cnt = 0;
    map(
        iter,
        #[requires(cnt@ == (*_prod).len() && cnt < usize::MAX)]
        #[ensures(cnt@ == old(cnt)@ + 1)]
        |x, _prod: Ghost<Seq<_>>| {
            cnt += 1;
            x
        },
    );
}
