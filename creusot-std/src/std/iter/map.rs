use crate::prelude::*;
#[cfg(creusot)]
use crate::{mode::Mode, resolve::structural_resolve};
use core::iter::Map;

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
            forall<mode: Mode> !mode.terminates() ==> next_precondition(mode, self.iter(), self.func())
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
    fn produces(self, mode: Mode, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func().hist_inv(succ.func())
            && exists<fs: Seq<&mut F>> fs.len() == visited.len()
            && exists<s: Seq<I::Item>>
                #[trigger(self.iter().produces(mode, s, succ.iter()))]
                s.len() == visited.len() && self.iter().produces(mode, s, succ.iter())
            && (forall<i> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == *fs[i])
            && if visited.len() == 0 { self.func() == succ.func() }
               else { *fs[0] == self.func() &&  ^fs[visited.len() - 1] == succ.func() }
            && forall<i> 0 <= i && i < visited.len() ==>
                 self.func().hist_inv(*fs[i]) && (*fs[i]).postcondition_mut(mode, (s[i],), ^fs[i], visited[i])
        }
    }

    #[logic(law)]
    #[ensures(forall<mode: Mode> self.produces(mode, Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(mode, ab, b))]
    #[requires(b.produces(mode, bc, c))]
    #[ensures(a.produces(mode, ab.concat(bc), c))]
    fn produces_trans(
        mode: Mode,
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    ) {
        proof_assert! {
            let ac = ab.concat(bc);
            let (fsab, sab) = produces_instantiate_existential(mode, a, ab, b);
            let (fsbc, sbc) = produces_instantiate_existential(mode, b, bc, c);
            let fs = fsab.concat(fsbc);
            let s = sab.concat(sbc);

            (forall<i> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == *fs[i])
            && if ac.len() == 0 { a.func() == c.func() }
               else { *fs[0] == a.func() &&  ^fs[ac.len() - 1] == c.func() }
            && forall<i> 0 <= i && i < ac.len() ==>
                 a.func().hist_inv(*fs[i])
                 && (*fs[i]).postcondition_mut(mode, (s[i],), ^fs[i], ac[i])
        }
    }
}

/// Get the witnesses for the existentials in `produces`
#[logic(prophetic)]
#[requires(this.produces(mode, visited, succ))]
#[ensures(result.0.len() == visited.len() && result.1.len() == visited.len()
    && this.iter().produces(mode, result.1, succ.iter())
    && (forall<i> 1 <= i && i < result.0.len() ==>  ^result.0[i - 1] == *result.0[i])
    && if visited.len() == 0 { this.func() == succ.func() }
       else { *result.0[0] == this.func() &&  ^result.0[visited.len() - 1] == succ.func() }
    && forall<i> 0 <= i && i < visited.len() ==>
         this.func().hist_inv(*result.0[i])
         && (*result.0[i]).postcondition_mut(mode, (result.1[i],), ^result.0[i], visited[i])
)]
fn produces_instantiate_existential<'a, I, B, F>(
    mode: Mode,
    this: Map<I, F>,
    visited: Seq<B>,
    succ: Map<I, F>,
) -> (Seq<&'a mut F>, Seq<I::Item>)
where
    I: IteratorSpec,
    F: FnMut(I::Item) -> B,
{
    creusot_std::logic::such_that(|(fs, s): (Seq<&mut F>, Seq<I::Item>)| {
        pearlite! {
            fs.len() == visited.len() && s.len() == visited.len()
            && this.iter().produces(mode, s, succ.iter())
            && (forall<i> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == *fs[i])
            && if visited.len() == 0 { this.func() == succ.func() }
               else { *fs[0] == this.func() &&  ^fs[visited.len() - 1] == succ.func() }
            && forall<i> 0 <= i && i < visited.len() ==>
                 this.func().hist_inv(*fs[i])
                 && (*fs[i]).postcondition_mut(mode, (s[i],), ^fs[i], visited[i])

        }
    })
}

#[logic(open, prophetic, inline)]
pub fn next_precondition<I: IteratorSpec, B, F: FnMut(I::Item) -> B>(
    mode: Mode,
    iter: I,
    func: F,
) -> bool {
    pearlite! {
        forall<e: I::Item, i: I>
            #[trigger(iter.produces(mode, Seq::singleton(e), i))]
            inv(e) && iter.produces(mode, Seq::singleton(e), i) ==>
            func.precondition(mode, (e,))
    }
}

#[logic(open, prophetic, inline)]
pub fn preservation<I: IteratorSpec, B, F: FnMut(I::Item) -> B>(iter: I, func: F) -> bool {
    pearlite! {
        forall<mode: Mode, s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
            #[trigger(iter.produces(mode, s.push_back(e1).push_back(e2), i), (*f).postcondition_mut(mode, (e1,), ^f, b))]
            !mode.terminates() ==>
            func.hist_inv(*f) ==>
            inv(s) && inv(e1) && inv(e2) && inv(f) ==>
            iter.produces(mode, s.push_back(e1).push_back(e2), i) ==>
            (*f).postcondition_mut(mode, (e1,), ^f, b) ==>
            (^f).precondition(mode, (e2, ))
    }
}

#[logic(open, prophetic, inline)]
pub fn reinitialize<I: IteratorSpec, B, F: FnMut(I::Item) -> B>() -> bool {
    pearlite! {
        forall<iter: &mut I, func: F>
            iter.completed()
            ==> (forall<mode: Mode> !mode.terminates() ==> next_precondition(mode, ^iter, func))
                && preservation(^iter, func)
    }
}
