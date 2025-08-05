extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

mod common;
pub use common::Iterator;

#[derive(Resolve)]
pub struct Enumerate<I: Iterator> {
    pub iter: I,
    pub count: usize,
}

impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
{
    type Item = (usize, I::Item);

    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() && (&mut self.count).resolve() }
    }

    #[open]
    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == o.count@ - self.count@
            && exists<s: Seq<I::Item>>
                   self.iter.produces(s, o.iter)
                && visited.len() == s.len()
                && forall<i> 0 <= i && i < s.len() ==> visited[i].0@ == self.count@ + i && visited[i].1 == s[i]
        }
    }

    #[logic(law)]
    #[open]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            None => None,
            Some(x) => {
                let n = self.count;
                self.count += 1;
                Some((n, x))
            }
        }
    }
}

impl<I> Invariant for Enumerate<I>
where
    I: Iterator,
{
    #[open]
    #[logic(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            (forall<s: Seq<I::Item>, i: I>
                #[trigger(self.iter.produces(s, i))]
                self.iter.produces(s, i) ==>
                self.count@ + s.len() < std::usize::MAX@)
            && (forall<i: &mut I> i.completed() ==> i.produces(Seq::empty(), ^i))
        }
    }
}

// These two requirements are here only to prove the absence of overflow.
#[requires(forall<i: &mut I> i.completed() ==> i.produces(Seq::empty(), ^i))]
#[requires(forall<s: Seq<I::Item>, i: I> iter.produces(s, i) ==> s.len() < std::usize::MAX@)]
#[ensures(result.iter == iter && result.count@ == 0)]
pub fn enumerate<I: Iterator>(iter: I) -> Enumerate<I> {
    Enumerate { iter, count: 0 }
}
