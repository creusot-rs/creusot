#[cfg(creusot)]
use crate::mode::Mode;
use crate::{invariant::Invariant, prelude::*, std::iter::ExactSizeIteratorSpec};
use core::iter::Iterator;

pub struct MapInv<I: Iterator, F> {
    pub iter: I,
    pub func: F,
    pub produced: Snapshot<Seq<I::Item>>,
}

impl<I: IteratorSpec, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> IteratorSpec
    for MapInv<I, F>
{
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            *(^self).produced == Seq::empty() &&
            self.iter.completed() && self.func == (^self).func
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

    #[logic(open, prophetic, inline)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func.hist_inv(succ.func)
            && exists<fs: Seq<F>> fs.len() == visited.len() + 1
            && exists<s: Seq<I::Item>> s.len() == visited.len() && self.iter.produces(s, succ.iter)
            && succ.produced.inner() == self.produced.concat(s)
            && fs[0] == self.func && fs[visited.len()] == succ.func
            && forall<i> 0 <= i && i < visited.len() ==>
                self.func.hist_inv(fs[i])
                && exists<mode: Mode> fs[i].postcondition_mut(mode, (s[i], Snapshot::new(self.produced.concat(s.subsequence(0, i)))), fs[i+1], visited[i])
        }
    }
}

impl<I: IteratorSpec, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Invariant
    for MapInv<I, F>
{
    #[logic(open, inline, prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            Self::preservation_inv(self.iter, self.func, *self.produced) &&
            Self::next_precondition(self.iter, self.func, *self.produced) &&
            forall<mode1, mode2, arg, f, f_fin, res>
                self.func.hist_inv(f) && f.postcondition_mut(mode1, arg, f_fin, res)
                ==> f.postcondition_mut(mode2, arg, f_fin, res)
        }
    }
}

impl<I: IteratorSpec, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Iterator for MapInv<I, F> {
    type Item = B;

    #[ensures(match result {
        None => self.completed(),
        Some(v) => (*self).produces_one(v, ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        let _old_self: Snapshot<Self> = snapshot! { *self };
        match self.iter.next() {
            Some(v) => {
                let produced = snapshot! { self.produced.push_back(v) };
                let r = (self.func)(v, self.produced);
                self.produced = produced;
                let _ = snapshot! { Self::produces_one_invariant };
                proof_assert! { _old_self.produces_one(r, *self) };
                let _ = self; // Make sure self is not resolve until here.
                Some(r)
            }
            None => {
                self.produced = snapshot! { Seq::empty() };
                None
            }
        }
    }

    #[ensures(|result, mode| I::size_hint.postcondition(mode, (&self.iter,), result))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I: IteratorSpec, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> MapInv<I, F> {
    #[logic(open, prophetic, inline)]
    pub fn next_precondition(iter: I, func: F, produced: Seq<I::Item>) -> bool {
        pearlite! {
            forall<e: I::Item, i: I>
                inv(e) && iter.produces(Seq::singleton(e), i) ==>
                forall<mode: Mode> func.precondition(mode, (e, Snapshot::new(produced)))
        }
    }

    #[logic(prophetic)]
    #[ensures(produced == Seq::empty() ==> result == Self::preservation(iter, func))]
    pub fn preservation_inv(iter: I, func: F, produced: Seq<I::Item>) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: F, f_fin: F, b: B, i: I, mode: Mode>
                func.hist_inv(f) ==>
                inv(s) && inv(e1) && inv(e2) && inv(f) ==>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                f.postcondition_mut(mode, (e1, Snapshot::new(produced.concat(s))), f_fin, b) ==>
                f_fin.precondition(mode, (e2, Snapshot::new(produced.concat(s).push_back(e1))))
        }
    }

    #[logic(open, prophetic, inline)]
    pub fn preservation(iter: I, func: F) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: F, f_fin: F, b: B, i: I, mode: Mode>
                func.hist_inv(f) ==>
                inv(s) && inv(e1) && inv(e2) && inv(f) ==>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                f.postcondition_mut(mode, (e1, Snapshot::new(s)), f_fin, b) ==>
                f_fin.precondition(mode, (e2, Snapshot::new(s.push_back(e1))))
        }
    }

    #[logic(open, prophetic, inline)]
    pub fn reinitialize() -> bool {
        pearlite! {
            forall<iter: &mut I, func: F>
                iter.completed() ==>
                Self::next_precondition(^iter, func, Seq::empty()) &&
                Self::preservation(^iter, func)
        }
    }

    #[logic]
    #[requires(inv(e))]
    #[requires(self.invariant())]
    #[requires(self.iter.produces(Seq::singleton(e), iter))]
    #[requires(exists<mode: Mode> self.func.postcondition_mut(mode, (e, self.produced), f_fin, r) )]
    #[ensures(Self::preservation_inv(iter, f_fin, self.produced.push_back(e)))]
    #[ensures(Self::next_precondition(iter, f_fin, self.produced.push_back(e)))]
    fn produces_one_invariant(self, e: I::Item, r: B, f_fin: F, iter: I) {
        proof_assert! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, i: I>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                self.iter.produces(s.push_front(e).push_back(e1).push_back(e2), i)
        }
    }

    #[logic(open, prophetic)] // TODO: inline (blocked on: binders in triggers are not supported in SMTLIB https://gitlab.inria.fr/why3/why3/-/work_items?sort=created_date&state=opened&search=trigger&first_page_size=20&show=eyJpaWQiOiI5MjciLCJmdWxsX3BhdGgiOiJ3aHkzL3doeTMiLCJpZCI6MTMxNTUwfQ%3D%3D)
    #[ensures(result == self.produces(Seq::singleton(visited), succ))]
    pub fn produces_one(self, visited: B, succ: Self) -> bool {
        pearlite! {
            exists<e: I::Item>
                self.iter.produces(Seq::singleton(e), succ.iter)
                && succ.produced.inner() == self.produced.push_back(e)
                && exists<mode: Mode> self.func.postcondition_mut(mode, (e, self.produced), succ.func, visited)
        }
    }
}

impl<I: ExactSizeIteratorSpec + IteratorSpec, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B>
    ExactSizeIterator for MapInv<I, F>
{
    #[ensures(|result, mode| Self::size_hint.postcondition(mode, (self,), (result, Some(result))))]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<I: ExactSizeIteratorSpec + IteratorSpec, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B>
    ExactSizeIteratorSpec for MapInv<I, F>
{
    #[logic(law)]
    #[requires(exists<mode: Mode> Self::size_hint.postcondition(mode, (self,), r))]
    #[ensures(r.1 == Some(r.0))]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {
        self.iter.size_hint_exact(r)
    }
}
