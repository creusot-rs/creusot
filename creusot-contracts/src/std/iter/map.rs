use crate::prelude::*;
#[cfg(creusot)]
use crate::resolve::structural_resolve;
use std::iter::Map;

pub trait MapExt<I, F> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn func(self) -> F;
}

impl<I, F> MapExt<I, F> for Map<I, F> {
    #[logic(opaque)]
    fn iter(self) -> I {
        dead
    }

    #[logic(opaque)]
    fn func(self) -> F {
        dead
    }
}

impl<I, F> Resolve for Map<I, F> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        resolve(self.iter()) && resolve(self.func())
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<I: IteratorSpec, B, F: FnMut(I::Item) -> B> Invariant for Map<I, F> {
    #[logic(prophetic)]
    #[ensures(result ==> inv(self.iter()) && inv(self.func()))]
    fn invariant(self) -> bool {
        pearlite! {
            inv(self.iter()) && inv(self.func()) &&
            reinitialize::<I, B, F>() &&
            preservation(self.iter(), self.func()) &&
            next_precondition(self.iter(), self.func())
        }
    }
}

impl<I: IteratorSpec, B, F: FnMut(I::Item) -> B> IteratorSpec for Map<I, F> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (exists<inner: &mut _> *inner == self.iter() && ^inner == (^self).iter() && inner.completed())
            && (*self).func() == (^self).func()
        }
    }

    #[logic(open, prophetic, inline)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func().hist_inv(succ.func())
            && exists<fs: Seq<&mut F>> fs.len() == visited.len()
            && exists<s: Seq<I::Item>>
                #[trigger(self.iter().produces(s, succ.iter()))]
                s.len() == visited.len() && self.iter().produces(s, succ.iter())
            && (forall<i> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == *fs[i])
            && if visited.len() == 0 { self.func() == succ.func() }
               else { *fs[0] == self.func() &&  ^fs[visited.len() - 1] == succ.func() }
            && forall<i> 0 <= i && i < visited.len() ==>
                 self.func().hist_inv(*fs[i])
                 && (*fs[i]).precondition((s[i],))
                 && (*fs[i]).postcondition_mut((s[i],), ^fs[i], visited[i])
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

#[logic(open, prophetic)]
pub fn next_precondition<I: IteratorSpec, B, F: FnMut(I::Item) -> B>(iter: I, func: F) -> bool {
    pearlite! {
        forall<e: I::Item, i: I>
            #[trigger(iter.produces(Seq::singleton(e), i))]
            iter.produces(Seq::singleton(e), i) ==>
            func.precondition((e,))
    }
}

#[logic(open, prophetic)]
pub fn preservation<I: IteratorSpec, B, F: FnMut(I::Item) -> B>(iter: I, func: F) -> bool {
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
pub fn reinitialize<I: IteratorSpec, B, F: FnMut(I::Item) -> B>() -> bool {
    pearlite! {
        forall<iter: &mut I, func: F>
            iter.completed() ==> next_precondition(^iter, func) && preservation(^iter, func)
    }
}
