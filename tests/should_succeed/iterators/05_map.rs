// WHY3PROVE
#![feature(unboxed_closures)]
extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

mod common;
use common::Iterator;

pub struct Map<I, F> {
    // The inner iterator
    pub iter: I,
    // The mapper
    pub func: F,
}

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {
    type Item = B;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() && (*self).func == (^self).func }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[logic(open, prophetic, inline)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func.hist_inv(succ.func)
            && exists<fs: Seq<&mut F>> fs.len() == visited.len()
            && exists<s: Seq<I::Item>>
                #[trigger(self.iter.produces(s, succ.iter))]
                s.len() == visited.len() && self.iter.produces(s, succ.iter)
            && (forall<i> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == *fs[i])
            && if visited.len() == 0 { self.func == succ.func }
               else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
            && forall<i> 0 <= i && i < visited.len() ==>
                 self.func.hist_inv(*fs[i])
                 && (*fs[i]).precondition((s[i],))
                 && (*fs[i]).postcondition_mut((s[i],), ^fs[i], visited[i])
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

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Map<I, F> {
    #[logic(open, prophetic)]
    pub fn next_precondition(iter: I, func: F) -> bool {
        pearlite! {
            forall<e: I::Item, i: I>
                #[trigger(iter.produces(Seq::singleton(e), i))]
                iter.produces(Seq::singleton(e), i) ==>
                func.precondition((e,))
        }
    }

    #[logic(open, prophetic)]
    pub fn preservation(iter: I, func: F) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                #[trigger(iter.produces(s.push_back(e1).push_back(e2), i), (*f).postcondition_mut((e1,), ^f, b))]
                func.hist_inv(*f) ==>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                (*f).precondition((e1,)) ==>
                (*f).postcondition_mut((e1,), ^f, b) ==>
                (^f).precondition((e2, ))
        }
    }

    #[logic(open, prophetic)]
    pub fn reinitialize() -> bool {
        pearlite! {
            forall<iter: &mut I, func: F>
                iter.completed() ==>
                Self::next_precondition(^iter, func) && Self::preservation(^iter, func)
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.iter.produces(Seq::singleton(e), iter))]
    #[requires(*f == self.func)]
    #[requires((*f).postcondition_mut((e,), ^f, r) )]
    #[ensures(Self::preservation(iter, ^f))]
    #[ensures(Self::next_precondition(iter, ^f))]
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
                #[trigger((*f).postcondition_mut((e,), ^f, visited))]
                *f == self.func && ^f == succ.func
                && self.iter.produces(Seq::singleton(e), succ.iter)
                && (*f).precondition((e,))
                && (*f).postcondition_mut((e,), ^f, visited)
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Invariant for Map<I, F> {
    #[logic(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            Self::preservation(self.iter, self.func) &&
            Self::next_precondition(self.iter, self.func)
        }
    }
}

#[requires(forall<e: I::Item, i2: I>
                iter.produces(Seq::singleton(e), i2) ==>
                func.precondition((e,)))]
#[requires(Map::<I, F>::reinitialize())]
#[requires(Map::<I, F>::preservation(iter, func))]
#[ensures(result == Map { iter, func })]
pub fn map<I: Iterator, B, F: FnMut(I::Item) -> B>(iter: I, func: F) -> Map<I, F> {
    Map { iter, func }
}
