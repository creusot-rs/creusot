#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{
    invariant::{inv, Invariant},
    logic::Mapping,
    *,
};

mod common;
use common::Iterator;

pub struct Filter<I: Iterator, F: FnMut(&I::Item) -> bool> {
    pub iter: I,
    pub func: F,
}

impl<I: Iterator, F: FnMut(&I::Item) -> bool> Invariant for Filter<I, F> {
    #[predicate(prophetic)]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            // trivial precondition: simplification for sake of proof complexity
            forall<f : F, i : &I::Item> f.precondition((i,)) &&
            // immutable state: simplification for sake of proof complexity
            (forall<f : F, g : F> f.unnest(g) ==> f == g) &&
            // plain-ness: this is a simplification as well, but a fairly major one for very minor loss of expressivity. In short all it says
            // is that we cannot `a == b` two mutable borrows.
            (forall<f : &mut F, g : &mut F, i :_, b :_> *f == *g && ^f == ^g ==> f.postcondition_mut((i,), b) == g.postcondition_mut((i,), b)) &&
            // precision of postcondition. In some sense this is not *necessary*, but without this we cannot prove that we return *all* elements
            // for all elements where the predicate evaluated to true, since we don't actually have access to the closure's return value directly,
            // only what the postcondition says about it.
            (forall<f : &mut F, i : _> f.postcondition_mut((i,), true) != f.postcondition_mut((i,), false))
        }
    }
}

impl<I: Iterator, F: FnMut(&I::Item) -> bool> Iterator for Filter<I, F> {
    type Item = I::Item;

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {(exists<e : &mut I, s: Seq<_>> self.iter.produces(s, *e) && e.completed()) && (*self).func == (^self).func }
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
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        // let f = |i : Int| if i < ab.len()
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func.unnest(succ.func) &&
            // f here is a mapping from indices of `visited` to those of `s`, where `s` is the whole sequence produced by the underlying iterator
            // Interestingly, Z3 guesses `f` quite readily but gives up *totally* on `s`. However, the addition of the final assertions on the correctness of the values
            // blocks z3's guess for `f`.
            exists<s : Seq<Self::Item>, f : Mapping<Int, Int>> self.iter.produces(s, succ.iter) &&
                // F is a monotone mapping
                (forall<i : _, j :_ > 0 <= i && i <= j && j < visited.len() ==> 0 <= f.get(i) && f.get(i) <= f.get(j) && f.get(j) < s.len()) &&
                (forall<i : _, > 0 <= i && i < visited.len() ==> visited[i] == s[f.get(i)]) &&

                (forall<bor_f : &mut F> *bor_f == self.func && ^bor_f == self.func ==>
                    forall< i : _> 0 <= i &&  i < s.len() ==>  (exists<j : _> 0 <= j && j < visited.len() && f.get(j) == i) == bor_f.postcondition_mut((&s[i],), true)
                )
        }
    }

    #[requires(inv(self))]
    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<I::Item> {
        let old_self = snapshot! { self};
        let mut produced = snapshot! { Seq::EMPTY };

        #[invariant(inv(self))]
        #[invariant(self.func == old_self.func)]
        #[invariant(forall<bor_f: &mut F>  *bor_f == self.func && ^ bor_f == self.func ==>
            forall<i : _> 0 <= i && i < produced.len() ==> bor_f.postcondition_mut((&produced[i],), false))]
        #[invariant(old_self.iter.produces(*produced, self.iter))]
        #[invariant(old_self.func.unnest(self.func))]
        while let Some(n) = self.iter.next() {
            produced = snapshot! { produced.push(n) };
            proof_assert!(old_self.iter.produces(*produced, self.iter));
            if (self.func)(&n) {
                return Some(n);
            }
        }

        None
    }
}

// Basic test to verify that closure properly satisfies invariant.
pub fn is_even<I: Iterator<Item = u32>>(iter: I) {
    let mut f = Filter {
        iter,
        func: #[ensures(result == (*x < 10u32))]
        |x| *x < 10,
    };

    let _ = f.next();
}
