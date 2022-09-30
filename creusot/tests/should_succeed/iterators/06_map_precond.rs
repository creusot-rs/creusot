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

    init_iter: Ghost<I>,
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Iterator for Map<I, I::Item, F> {
    type Item = B;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            *(^self).init_iter == (^self).iter && *(^self).produced == Seq::EMPTY &&
            (exists<iter : &mut I> *iter == self.iter && ^iter == (^self).iter && iter.completed())
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
            (self.produced.len() + visited.len() == succ.produced.len()
            && succ.produced.subsequence(0, self.produced.len()).ext_eq(*self.produced)
            && self.init_iter == succ.init_iter)
            && self.iter.produces(succ.produced.subsequence(self.produced.len(), succ.produced.len()), succ.iter )
            && exists<fs : Seq<&mut F>>
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
            self.init_iter.invariant() && self.iter.invariant() &&
            self.init_iter.produces(*self.produced, self.iter) &&
            self.has_precond(self.iter, Seq::EMPTY)
        }
    }

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    #[maintains((mut self).invariant())]
    fn next(&mut self) -> Option<Self::Item> {
        let _ = ghost! { #[allow(path_statements)] {Seq::<I::Item>::left_neutral; Self::inner_produces_ag; Self::inner_ext_trans;} };
        let produced = ghost! { *self.produced };
        match self.iter.next() {
            Some(v) => {
                self.produced = ghost! { produced.push(v) };
                Some((self.func)(v, produced))
            }
            None => {
                self.init_iter = ghost! { self.iter };
                self.produced = ghost! { Seq::EMPTY };
                None
            }
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Map<I, I::Item, F> {
    #[predicate]
    fn inner_extension(self, other: Self) -> bool {
        (self.init_iter == other.init_iter)
            && other.produced.len() >= self.produced.len()
            && other.produced.subsequence(0, self.produced.len()).ext_eq(*self.produced)
            && self.iter.produces(
                other.produced.subsequence(self.produced.len(), other.produced.len()),
                other.iter,
            )
    }

    // Probably needs to be reworked
    #[predicate]
    fn has_precond(self, start: I, with: Seq<I::Item>) -> bool {
        pearlite! {
            forall<e : I::Item, i2 : I>
                i2.invariant() ==>
                start.produces(with.push(e), i2) ==> self.func.precondition((e, self.produced))
        }
    }

    #[logic]
    #[requires(a.produces(s, b))]
    #[ensures(a.inner_extension(b))]
    fn inner_produces_ag(a: Self, s: Seq<B>, b: Self) {}

    #[logic]
    #[requires(a.iter.invariant())]
    #[requires(b.iter.invariant())]
    #[requires(c.iter.invariant())]
    #[requires(a.inner_extension(b))]
    #[requires(b.inner_extension(c))]
    #[ensures(a.inner_extension(c))]
    fn inner_ext_trans(a: Self, b: Self, c: Self) {
        // assert { b.produced[a.len()..] ++ c.produced[b.len()..] == c.produed[a.len()..]}
    }

    #[logic]
    fn new_logic(iter: I, func: F) -> Self {
        Map { iter, func, init_iter: Ghost(iter), produced: Ghost(Seq::EMPTY) }
    }

    #[predicate]
    fn reinitialize() -> bool {
        pearlite! {
            forall<reset : &mut Map<I, _, F>>
                reset.completed() ==>
                (^reset).iter.invariant() ==>
                (^reset).has_precond((^reset).iter, Seq::EMPTY) &&
                (^reset).preservation()
        }
    }

    #[predicate]
    fn preservation(self) -> bool {
        pearlite! {
            forall<initial: Self>
                self.inner_extension(initial) ==>
                initial.has_precond(initial.iter, Seq::EMPTY)  ==>
                initial.iter.invariant() ==>
                // post condition implies invariant
                forall<n: Self, b: B>
                    n.iter.invariant() ==>
                    initial.produces(Seq::singleton(b), n) ==>
                        n.has_precond(n.iter, Seq::EMPTY)

        }
    }
}

#[requires(forall<e : I::Item, i2 : I> i2.invariant() ==> iter.produces(Seq::singleton(e), i2) ==> func.precondition((e, Ghost(Seq::EMPTY))))]
#[requires(Map::<I, _, F>::reinitialize())]
#[requires(iter.invariant())]
#[requires(
    forall<initial: Map<I, _, _>>
    initial.iter.invariant() ==>
    Map::new_logic(iter, func).inner_extension(initial) ==>
    initial.has_precond(initial.iter, Seq::EMPTY) ==>
    forall<n: Map<I, _, _>, b: B> n.iter.invariant() ==> initial.produces(Seq::singleton(b), n) ==>
        n.has_precond(iter, *n.produced)
)]
#[ensures(result.invariant())]
#[ensures(result == Map { init_iter: Ghost(iter), iter, func, produced: Ghost(Seq::EMPTY) })]
pub fn map<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B>(
    iter: I,
    func: F,
) -> Map<I, I::Item, F> {
    Map { init_iter: ghost! {iter}, iter, func, produced: ghost! {Seq::EMPTY} }
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
        #[requires(@cnt == (*prod).len() && cnt < usize::MAX)]
        #[ensures(@cnt == @old(cnt) + 1 && @cnt == (*prod).len() + 1)]
        |x, prod: Ghost<Seq<_>>| {
            cnt += 1;
            x
        },
    );
}
