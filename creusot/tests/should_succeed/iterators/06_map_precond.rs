#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{
    invariant::{inv, Invariant},
    *,
};

mod common;
use common::Iterator;

// FIXME: make it Map<I, A, F> again
pub struct Map<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> {
    iter: I,
    func: F,
    produced: Snapshot<Seq<I::Item>>,
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Iterator for Map<I, B, F> {
    type Item = B;

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            *(^self).produced == Seq::EMPTY &&
            self.iter.completed() && self.func == (^self).func
        }
    }

    #[law]
    #[open]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[open]
    #[predicate(prophetic)]
    #[why3::attr = "inline:trivial"]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func.unnest(succ.func)
            && exists<s : Seq<I::Item>> inv(s) && s.len() == visited.len() && self.iter.produces(s, succ.iter)
            && succ.produced.inner() == self.produced.concat(s)
            && exists<fs: Seq<&mut F>> inv(fs) && fs.len() == visited.len()
            && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
            && if visited.len() == 0 { self.func == succ.func }
               else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
            && forall<i : Int> 0 <= i && i < visited.len() ==>
                 self.func.unnest(*fs[i])
                 && (*fs[i]).precondition((s[i], Snapshot::new(self.produced.concat(s.subsequence(0, i)))))
                 && fs[i].postcondition_mut((s[i], Snapshot::new(self.produced.concat(s.subsequence(0, i)))), visited[i])
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
                let produced = snapshot! { self.produced.push(v) };
                let r = (self.func)(v, self.produced);
                self.produced = produced;
                snapshot! { Self::produces_one_invariant };
                Some(r)
            }
            None => {
                self.produced = snapshot! { Seq::EMPTY };
                None
            }
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Map<I, B, F> {
    #[predicate(prophetic)]
    fn next_precondition(iter: I, func: F, produced: Seq<I::Item>) -> bool {
        pearlite! {
            forall<e: I::Item, i: I>
                iter.produces(Seq::singleton(e), i) ==>
                func.precondition((e, Snapshot::new(produced)))
        }
    }

    #[predicate(prophetic)]
    #[ensures(produced == Seq::EMPTY ==> result == Self::preservation(iter, func))]
    fn preservation_inv(iter: I, func: F, produced: Seq<I::Item>) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                func.unnest(*f) ==>
                iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Snapshot::new(produced.concat(s)))) ==>
                f.postcondition_mut((e1, Snapshot::new(produced.concat(s))), b) ==>
                (^f).precondition((e2, Snapshot::new(produced.concat(s).push(e1))))
        }
    }

    #[predicate(prophetic)]
    fn preservation(iter: I, func: F) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                func.unnest(*f) ==>
                iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Snapshot::new(s))) ==>
                f.postcondition_mut((e1, Snapshot::new(s)), b) ==>
                (^f).precondition((e2, Snapshot::new(s.push(e1))))
        }
    }

    #[predicate(prophetic)]
    fn reinitialize() -> bool {
        pearlite! {
            forall<iter: &mut I, func: F>
                iter.completed() ==>
                Self::next_precondition(^iter, func, Seq::EMPTY) &&
                Self::preservation(^iter, func)
        }
    }

    #[logic]
    #[requires(inv(self))]
    #[requires(self.iter.produces(Seq::singleton(e), iter))]
    #[requires(*f == self.func)]
    #[requires(f.postcondition_mut((e, self.produced), r) )]
    #[ensures(Self::preservation_inv(iter, ^f, self.produced.push(e)))]
    #[ensures(Self::next_precondition(iter, ^f, self.produced.push(e)))]
    fn produces_one_invariant(self, e: I::Item, r: B, f: &mut F, iter: I) {
        proof_assert! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, i: I>
                iter.produces(s.push(e1).push(e2), i) ==>
                self.iter.produces(Seq::singleton(e).concat(s).push(e1).push(e2), i)
        }
    }

    #[predicate(prophetic)]
    #[ensures(result == self.produces(Seq::singleton(visited), succ))]
    fn produces_one(self, visited: B, succ: Self) -> bool {
        pearlite! {
            exists<f: &mut F> inv(f) && *f == self.func && ^f == succ.func
            && exists<e: I::Item> inv(e)
                && self.iter.produces(Seq::singleton(e), succ.iter)
                && succ.produced.inner() == self.produced.push(e)
                && (*f).precondition((e, self.produced))
                && f.postcondition_mut((e, self.produced), visited)
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Invariant for Map<I, B, F> {
    // Should not quantify over self or the `invariant` cannot be made into a type invariant
    #[predicate(prophetic)]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            Self::preservation_inv(self.iter, self.func, *self.produced) &&
            Self::next_precondition(self.iter, self.func, *self.produced)
        }
    }
}

#[requires(forall<e : I::Item, i2 : I> iter.produces(Seq::singleton(e), i2) ==> func.precondition((e, Snapshot::new(Seq::EMPTY))))]
#[requires(Map::<I, B, F>::reinitialize())]
#[requires(Map::<I, B, F>::preservation(iter, func))]
#[ensures(result == Map { iter, func, produced: Snapshot::new(Seq::EMPTY) })]
pub fn map<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B>(
    iter: I,
    func: F,
) -> Map<I, B, F> {
    Map { iter, func, produced: snapshot! {Seq::EMPTY} }
}

pub fn identity<I: Iterator>(iter: I) {
    map(iter, |x, _| x);
}

#[requires(forall<done : &mut U> done.completed() ==> forall<next : U, steps: Seq<_>> (^done).produces(steps, next) ==> steps == Seq::EMPTY && ^done == next)]
#[requires(forall<prod : _, fin: U> iter.produces(prod, fin) ==>
    forall<x : _> 0 <= x && x < prod.len() ==> prod[x] <= 10u32
)]
pub fn increment<U: Iterator<Item = u32>>(iter: U) {
    let i = map(
        iter,
        #[requires(x@ <= 15)]
        #[ensures(result@ == x@+1)]
        |x: u32, _| x + 1,
    );

    proof_assert! {
        forall<prod : _, fin: Map< _, _, _>> i.produces(prod, fin) ==>
            forall<x : _> 0 <= x && x < prod.len() ==> prod[x] <= 11u32
    };
}

#[requires(forall<done : &mut I> done.completed() ==> forall<next : I, steps: Seq<_>> (^done).produces(steps, next) ==> steps == Seq::EMPTY && ^done == next)]
#[requires(forall<prod : _, fin: I> iter.produces(prod, fin) ==> prod.len() <= usize::MAX@)]
pub fn counter<I: Iterator<Item = u32>>(iter: I) {
    let mut cnt = 0;
    map(
        iter,
        #[requires(cnt@ == (*_prod).len() && cnt < usize::MAX)]
        #[ensures(cnt@ == old(cnt)@ + 1)]
        |x, _prod: Snapshot<Seq<_>>| {
            cnt += 1;
            x
        },
    );
}
