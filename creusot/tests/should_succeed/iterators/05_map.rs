#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{
    logic::{Int, Seq},
    std::ops::*,
    *,
};

mod common;
use common::*;

struct Map<I, F> {
    // The inner iterator
    iter: I,
    // The mapper
    func: F,
}

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {
    type Item = B;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() && self.func == (^self).func }
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
            self.func.unnest(succ.func)
            && exists<s : Seq<_>> s.len() == visited.len() && self.iter.produces(s, succ.iter )
                && exists<fs: Seq<&mut F>>
                    fs.len() == visited.len()
                    && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
                    && if visited.len() == 0 { self.func == succ.func }
                       else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
                    && forall<i : Int> 0 <= i && i < visited.len() ==>
                        fs[i].postcondition_mut((s[i],), visited[i])
        }
    }

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

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces_one(v, ^self)
    })]
    #[maintains((mut self).invariant())]
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                proof_assert! { self.func.precondition((v,)) };
                ghost! { Self::produces_one_invariant };

                Some((self.func)(v))
            }
            None => None,
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Map<I, F> {
    #[predicate]
    fn next_precondition(self) -> bool {
        pearlite! {
            forall<e: I::Item, i: I> i.invariant() ==>
                self.iter.produces(Seq::singleton(e), i) ==> self.func.precondition((e,))
        }
    }

    #[predicate]
    fn reinitialize() -> bool {
        pearlite! {
            forall<reset : &mut Map<I, F>> (^reset).iter.invariant() ==>
                reset.completed() ==> (^reset).next_precondition() && Self::preservation((^reset).iter)
        }
    }

    #[predicate]
    #[ensures(result == Self::preservation(self.iter))]
    fn preservation_inv(self) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                i.invariant() ==>
                self.iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1,)) ==>
                f.postcondition_mut((e1,), b) ==>
                (^f).precondition((e2,))
        }
    }

    #[predicate]
    fn preservation(iter: I) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                i.invariant() ==>
                iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1,)) ==>
                f.postcondition_mut((e1,), b) ==>
                (^f).precondition((e2, ))
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
            self.func.unnest(succ.func) &&
            exists<f: &mut F> *f == self.func && ^f == succ.func
            && { exists<e : _>
                 self.iter.produces(Seq::singleton(e), succ.iter)
                 && f.postcondition_mut((e,), visited) }
        }
    }
}
