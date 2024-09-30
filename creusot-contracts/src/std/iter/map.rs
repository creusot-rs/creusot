use crate::{
    inv, logic::*, macros::*, resolve, std::ops::*, structural_resolve, Invariant, Iterator,
    Resolve,
};
use std::iter::Map;

pub trait MapExt<I, F> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn func(self) -> F;
}

impl<I, F> MapExt<I, F> for Map<I, F> {
    #[trusted]
    #[logic]
    #[open(self)]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[ensures(inv(self) ==> inv(result))]
    fn func(self) -> F {
        absurd
    }
}

impl<I, F> Resolve for Map<I, F> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        resolve(&self.iter()) && resolve(&self.func())
    }

    #[trusted]
    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<B, I, F> Iterator for Map<I, F>
where
    I: Iterator,
    Self: ::std::iter::Iterator<Item = B>,
    F: FnMut(I::Item) -> B,
{
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
        (exists<inner : &mut _> inv(inner) && *inner == self.iter() && ^inner == (^self).iter()
            && inner.completed()) && (*self).func() == (^self).func() }
    }

    #[open]
    #[predicate(prophetic)]
    #[why3::attr = "inline:trivial"]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func().unnest(succ.func())
            && exists<fs: Seq<&mut F>> inv(fs) && fs.len() == visited.len()
            && exists<s : Seq<I::Item>>
                #![trigger self.iter().produces(s, succ.iter())]
                inv(s) && s.len() == visited.len() && self.iter().produces(s, succ.iter())
            && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == *fs[i])
            && if visited.len() == 0 { self.func() == succ.func() }
               else { *fs[0] == self.func() &&  ^fs[visited.len() - 1] == succ.func() }
            && forall<i : Int> 0 <= i && i < visited.len() ==>
                 self.func().unnest(*fs[i])
                 && (*fs[i]).precondition((s[i],))
                 && fs[i].postcondition_mut((s[i],), visited[i])
        }
    }

    #[law]
    #[open(self)]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

#[open]
#[predicate(prophetic)]
pub fn next_precondition<I, B, F>(iter: I, func: F) -> bool
where
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    pearlite! {
        forall<e: I::Item, i: I>
            #![trigger iter.produces(Seq::singleton(e), i)]
            inv(e) && inv(i) ==>
            iter.produces(Seq::singleton(e), i) ==>
            func.precondition((e,))
    }
}

#[open]
#[predicate(prophetic)]
pub fn preservation<I, B, F>(iter: I, func: F) -> bool
where
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    pearlite! {
        forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
            #![trigger iter.produces(s.push(e1).push(e2), i), f.postcondition_mut((e1,), b)]
            inv(s) && inv(e1) && inv(e2) && inv(f) && inv(i) && func.unnest(*f) ==>
            iter.produces(s.push(e1).push(e2), i) ==>
            (*f).precondition((e1,)) ==>
            f.postcondition_mut((e1,), b) ==>
            (^f).precondition((e2, ))
    }
}

#[open]
#[predicate(prophetic)]
pub fn reinitialize<I, B, F>() -> bool
where
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    pearlite! {
        forall<iter: &mut I, func: F>
            inv(iter) && inv(func) ==>
            iter.completed() ==>
            next_precondition(^iter, func) && preservation(^iter, func)
    }
}
