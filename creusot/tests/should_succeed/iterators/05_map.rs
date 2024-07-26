#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{invariant::Invariant, *};

mod common;
use common::Iterator;

// FIXME: make it Map<I, F> again
pub struct Map<I: Iterator, B, F: FnMut(I::Item) -> B> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,
}

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Iterator for Map<I, B, F> {
    type Item = B;

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() && (*self).func == (^self).func }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
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
            && exists<s : Seq<I::Item>> s.len() == visited.len() && self.iter.produces(s, succ.iter)
            && exists<fs: Seq<&mut F>> fs.len() == visited.len()
            && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == *fs[i])
            && if visited.len() == 0 { self.func == succ.func }
               else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
            && forall<i : Int> 0 <= i && i < visited.len() ==>
                 self.func.unnest(*fs[i])
                 && (*fs[i]).precondition((s[i],))
                 && fs[i].postcondition_mut((s[i],), visited[i])
        }
    }

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces_one(v, ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                proof_assert! { self.func.precondition((v,)) };
                snapshot! { Self::produces_one_invariant };
                Some((self.func)(v))
            }
            None => None,
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Map<I, B, F> {
    #[predicate(prophetic)]
    fn next_precondition(iter: I, func: F) -> bool {
        pearlite! {
            forall<e: I::Item, i: I> iter.produces(Seq::singleton(e), i) ==> func.precondition((e,))
        }
    }

    #[predicate(prophetic)]
    fn preservation(iter: I, func: F) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                func.unnest(*f) ==>
                iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1,)) ==>
                f.postcondition_mut((e1,), b) ==>
                (^f).precondition((e2, ))
        }
    }

    #[predicate(prophetic)]
    fn reinitialize() -> bool {
        pearlite! {
            forall<iter: &mut I, func: F>
                iter.completed() ==>
                Self::next_precondition(^iter, func) && Self::preservation(^iter, func)
        }
    }

    #[logic]
    #[requires(self.iter.produces(Seq::singleton(e), iter))]
    #[requires(*f == self.func)]
    #[requires(f.postcondition_mut((e,), r) )]
    #[ensures(Self::preservation(iter, ^f))]
    #[ensures(Self::next_precondition(iter, ^f))]
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
            exists<f: &mut F> *f == self.func && ^f == succ.func
            && { exists<e : I::Item> self.iter.produces(Seq::singleton(e), succ.iter)
                 && (*f).precondition((e,))
                 && f.postcondition_mut((e,), visited) }
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Invariant for Map<I, B, F> {
    // Should not quantify over self or the `invariant` cannot be made into a type invariant
    #[predicate(prophetic)]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            Self::preservation(self.iter, self.func) &&
            Self::next_precondition(self.iter, self.func)
        }
    }
}

#[requires(forall<e : I::Item, i2 : I> iter.produces(Seq::singleton(e), i2) ==> func.precondition((e,)))]
#[requires(Map::<I, B, F>::reinitialize())]
#[requires(Map::<I, B, F>::preservation(iter, func))]
#[ensures(result == Map { iter, func })]
pub fn map<I: Iterator, B, F: FnMut(I::Item) -> B>(iter: I, func: F) -> Map<I, B, F> {
    Map { iter, func }
}
