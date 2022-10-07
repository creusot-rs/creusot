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
        pearlite! {
            exists<iter : &mut _> *iter == self.iter && ^iter == (^self).iter && iter.completed()
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
            exists<items : Seq<I::Item>, fs : Seq<&mut F>>
                   self.iter.produces(items, succ.iter )

                && items.len() == fs.len()
                && fs.len() == visited.len()

                && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
                && (visited.len() > 0 ==>
                        * fs[0] == self.func
                    &&  ^ fs[visited.len() - 1] == succ.func)
                && (visited.len() == 0 ==> self.func == succ.func)

                && forall<i : Int>
                    0 <= i && i < visited.len() ==>
                    fs[i].postcondition_mut((items[i],), visited[i])
        }
    }

    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            self.iter.invariant() && (forall<f : F, e: _> f.precondition((e,)))
        }
    }

    #[maintains((mut self).invariant())]
    #[ensures(match result {
      None => (*self).completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }
}
