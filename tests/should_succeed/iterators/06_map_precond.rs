// WHY3PROVE
#![feature(unboxed_closures)]
extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

mod common;
use common::Iterator;

#[derive(Resolve)]
pub struct Map<I: Iterator, F> {
    pub iter: I,
    pub func: F,
    pub produced: Snapshot<Seq<I::Item>>,
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Iterator for Map<I, F> {
    type Item = B;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            *(^self).produced == Seq::empty() &&
            self.iter.completed() && self.func == (^self).func
        }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func.hist_inv(succ.func)
            && exists<fs: Seq<&mut F>> fs.len() == visited.len()
            && exists<s: Seq<I::Item>>
                #[trigger(self.iter.produces(s, succ.iter))]
                s.len() == visited.len() && self.iter.produces(s, succ.iter)
            && succ.produced.inner() == self.produced.concat(s)
            && (forall<i> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
            && if visited.len() == 0 { self.func == succ.func }
               else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
            && forall<i> 0 <= i && i < visited.len() ==>
                 self.func.hist_inv(*fs[i])
                 && (*fs[i]).precondition((s[i], Snapshot::new(self.produced.concat(s.subsequence(0, i)))))
                 && (*fs[i]).postcondition_mut((s[i], Snapshot::new(self.produced.concat(s.subsequence(0, i)))), ^fs[i], visited[i])
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
                let produced = snapshot! { self.produced.push_back(v) };
                let r = (self.func)(v, self.produced);
                self.produced = produced;
                snapshot! { Self::produces_one_invariant };
                Some(r)
            }
            None => {
                self.produced = snapshot! { Seq::empty() };
                None
            }
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Map<I, F> {
    #[logic(open, prophetic)]
    pub fn next_precondition(iter: I, func: F, produced: Seq<I::Item>) -> bool {
        pearlite! {
            forall<e: I::Item, i: I>
                #[trigger(iter.produces(Seq::singleton(e), i))]
                iter.produces(Seq::singleton(e), i) ==>
                func.precondition((e, Snapshot::new(produced)))
        }
    }

    #[logic(prophetic)]
    #[ensures(produced == Seq::empty() ==> result == Self::preservation(iter, func))]
    fn preservation_inv(iter: I, func: F, produced: Seq<I::Item>) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                #[trigger(iter.produces(s.push_back(e1).push_back(e2), i),(*f).postcondition_mut((e1, Snapshot::new(produced.concat(s))), ^f, b))]
                func.hist_inv(*f) ==>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                (*f).precondition((e1, Snapshot::new(produced.concat(s)))) ==>
                (*f).postcondition_mut((e1, Snapshot::new(produced.concat(s))), ^f, b) ==>
                (^f).precondition((e2, Snapshot::new(produced.concat(s).push_back(e1))))
        }
    }

    #[logic(open, prophetic)]
    pub fn preservation(iter: I, func: F) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                func.hist_inv(*f) ==>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                (*f).precondition((e1, Snapshot::new(s))) ==>
                (*f).postcondition_mut((e1, Snapshot::new(s)), ^f, b) ==>
                (^f).precondition((e2, Snapshot::new(s.push_back(e1))))
        }
    }

    #[logic(open, prophetic)]
    pub fn reinitialize() -> bool {
        pearlite! {
            forall<iter: &mut I, func: F>
                iter.completed() ==>
                Self::next_precondition(^iter, func, Seq::empty()) &&
                Self::preservation(^iter, func)
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.iter.produces(Seq::singleton(e), iter))]
    #[requires(*f == self.func)]
    #[requires((*f).postcondition_mut((e, self.produced), ^f, r) )]
    #[ensures(Self::preservation_inv(iter, ^f, self.produced.push_back(e)))]
    #[ensures(Self::next_precondition(iter, ^f, self.produced.push_back(e)))]
    fn produces_one_invariant(self, e: I::Item, r: B, f: &mut F, iter: I) {
        proof_assert! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, i: I>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                self.iter.produces(Seq::singleton(e).concat(s).push_back(e1).push_back(e2), i)
        }
    }

    #[logic(open, prophetic)]
    #[ensures(result == self.produces(Seq::singleton(visited), succ))]
    pub fn produces_one(self, visited: B, succ: Self) -> bool {
        pearlite! {
            exists<f: &mut F, e: I::Item>
                #[trigger((*f).postcondition_mut((e, self.produced), ^f, visited))]
                *f == self.func && ^f == succ.func
                && self.iter.produces(Seq::singleton(e), succ.iter)
                && succ.produced.inner() == self.produced.push_back(e)
                && (*f).precondition((e, self.produced))
                && (*f).postcondition_mut((e, self.produced), ^f, visited)
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Invariant for Map<I, F> {
    #[logic(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            Self::preservation_inv(self.iter, self.func, *self.produced) &&
            Self::next_precondition(self.iter, self.func, *self.produced)
        }
    }
}

#[requires(forall<e: I::Item, i2: I>
                iter.produces(Seq::singleton(e), i2) ==>
                func.precondition((e, Snapshot::new(Seq::empty()))))]
#[requires(Map::<I, F>::reinitialize())]
#[requires(Map::<I, F>::preservation(iter, func))]
#[ensures(result == Map { iter, func, produced: Snapshot::new(Seq::empty()) })]
pub fn map<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B>(
    iter: I,
    func: F,
) -> Map<I, F> {
    Map { iter, func, produced: snapshot! {Seq::empty()} }
}

pub fn identity<I: Iterator>(iter: I) {
    map(iter, |x, _| x);
}

#[requires(forall<done: &mut U> done.completed() ==> forall<next, steps> (^done).produces(steps, next) ==> steps == Seq::empty() && ^done == next)]
#[requires(forall<prod, fin> iter.produces(prod, fin) ==>
    forall<x> 0 <= x && x < prod.len() ==> prod[x] <= 10u32
)]
pub fn increment<U: Iterator<Item = u32>>(iter: U) {
    let i = map(iter, |x: u32, _| x + 1);

    proof_assert! {
        forall<prod, fin> i.produces(prod, fin) ==>
            forall<x> 0 <= x && x < prod.len() ==> prod[x] <= 11u32
    };
}

#[requires(forall<done: &mut I> done.completed() ==> forall<next, steps> (^done).produces(steps, next) ==> steps == Seq::empty() && ^done == next)]
#[requires(forall<prod, fin> iter.produces(prod, fin) ==> prod.len() <= usize::MAX@)]
pub fn counter<I: Iterator<Item = u32>>(iter: I) {
    let mut cnt: usize = 0;
    map(iter, |x, _prod: Snapshot<Seq<_>>| {
        proof_assert!(cnt@ == _prod.len());
        cnt += 1;
        x
    });
}
