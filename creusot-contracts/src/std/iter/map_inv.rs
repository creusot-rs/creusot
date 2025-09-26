#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{invariant::Invariant, *};

pub struct MapInv<I, B, F> {
    pub iter: I,
    pub func: F,
    pub produced: Snapshot<Seq<B>>,
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Iterator
    for MapInv<I, I::Item, F>
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
            && exists<fs: Seq<&mut F>> fs.len() == visited.len()
            && exists<s: Seq<I::Item>> s.len() == visited.len() && self.iter.produces(s, succ.iter)
            && succ.produced.inner() == self.produced.concat(s)
            && (forall<i> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
            && if visited.len() == 0 { self.func == succ.func }
               else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
            && forall<i> 0 <= i && i < visited.len() ==>
                 self.func.hist_inv(*fs[i])
                 && (*fs[i]).precondition((s[i], Snapshot::new(self.produced.concat(s.subsequence(0, i)))))
                 && (*fs[i]).postcondition_mut((s[i], Snapshot::new(self.produced.concat(s.subsequence(0, i)))), ^fs[i], visited[i])
        }
    }
}

impl<I, B, F> Resolve for MapInv<I, B, F> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        resolve(self.iter) && resolve(self.func)
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> Invariant
    for MapInv<I, I::Item, F>
{
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            Self::preservation_inv(self.iter, self.func, *self.produced) &&
            Self::next_precondition(self.iter, self.func, *self.produced)
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> ::std::iter::Iterator
    for MapInv<I, I::Item, F>
{
    type Item = B;

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces_one(v, ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        let old_self: Snapshot<Self> = snapshot! { *self };
        match self.iter.next() {
            Some(v) => {
                proof_assert! { self.func.precondition((v, self.produced)) };
                let produced = snapshot! { self.produced.push_back(v) };
                let r = (self.func)(v, self.produced);
                self.produced = produced;
                #[allow(path_statements)]
                let _ = snapshot! { Self::produces_one_invariant };
                proof_assert! { old_self.produces_one(r, *self) };
                let _ = self; // Make sure self is not resolve until here.
                Some(r)
            }
            None => {
                self.produced = snapshot! { Seq::empty() };
                None
            }
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Snapshot<Seq<I::Item>>) -> B> MapInv<I, I::Item, F> {
    #[logic(open, prophetic)]
    pub fn next_precondition(iter: I, func: F, produced: Seq<I::Item>) -> bool {
        pearlite! {
            forall<e: I::Item, i: I>
                iter.produces(Seq::singleton(e), i) ==>
                func.precondition((e, Snapshot::new(produced)))
        }
    }

    #[logic(prophetic)]
    #[ensures(produced == Seq::empty() ==> result == Self::preservation(iter, func))]
    pub fn preservation_inv(iter: I, func: F, produced: Seq<I::Item>) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                func.hist_inv(*f) ==>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                (*f).precondition((e1, Snapshot::new(produced.concat(s)))) ==>
                (*f).postcondition_mut((e1, Snapshot::new(produced.concat(s))), ^f, b) ==>
                (^f).precondition((e2, Snapshot::new(produced.concat(s).push_back(e1))))
        }
    }

    #[logic(open, prophetic)]
    pub fn preservation(iter: I, func: F) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                func.hist_inv(*f) ==>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                (*f).precondition((e1, Snapshot::new(s))) ==>
                (*f).postcondition_mut((e1, Snapshot::new(s)), ^f, b) ==>
                (^f).precondition((e2, Snapshot::new(s.push_back(e1))))
        }
    }

    #[logic(open, prophetic)]
    pub fn reinitialize() -> bool {
        pearlite! {
            forall<iter: &mut I, func: F>
                iter.completed() ==>
                Self::next_precondition(^iter, func, Seq::empty()) &&
                Self::preservation(^iter, func)
        }
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(self.iter.produces(Seq::singleton(e), iter))]
    #[requires(*f == self.func)]
    #[requires((*f).postcondition_mut((e, self.produced), ^f, r) )]
    #[ensures(Self::preservation_inv(iter, ^f, self.produced.push_back(e)))]
    #[ensures(Self::next_precondition(iter, ^f, self.produced.push_back(e)))]
    fn produces_one_invariant(self, e: I::Item, r: B, f: &mut F, iter: I) {
        proof_assert! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, i: I>
                iter.produces(s.push_back(e1).push_back(e2), i) ==>
                self.iter.produces(s.push_front(e).push_back(e1).push_back(e2), i)
        }
    }

    #[logic(open, prophetic)]
    #[ensures(result == self.produces(Seq::singleton(visited), succ))]
    pub fn produces_one(self, visited: B, succ: Self) -> bool {
        pearlite! {
            exists<f: &mut F, e: I::Item>
                *f == self.func && ^f == succ.func
                && self.iter.produces(Seq::singleton(e), succ.iter)
                && succ.produced.inner() == self.produced.push_back(e)
                && (*f).precondition((e, self.produced))
                && (*f).postcondition_mut((e, self.produced), ^f, visited)
        }
    }
}
