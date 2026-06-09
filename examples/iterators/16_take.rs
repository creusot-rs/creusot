extern crate creusot_std;
use creusot_std::prelude::*;

pub mod common;
pub use common::{ExactSizeIterator, Iterator};

pub struct Take<I: Iterator> {
    pub iter: I,
    pub n: usize,
}

impl<I> Iterator for Take<I>
where
    I: Iterator,
{
    type Item = I::Item;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (*self).n@ == 0 && resolve(self) ||
            (*self).n@ > 0 && (*self).n@ == (^self).n@ + 1 && self.iter.completed()
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.n@ == o.n@ + visited.len() && self.iter.produces(visited, o.iter)
        }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<I::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }

    #[ensures(self.n > 0usize ==> exists<r>
        I::size_hint.postcondition((&self.iter,), r) &&
        (r.0 <= self.n ==> result.0 == r.0) &&
        (r.0 >= self.n ==> result.0 == self.n) &&
        match r.1 {
            Some(ub) =>
                (ub <= self.n ==> result.1 == Some(ub)) &&
                (ub >= self.n ==> result.1 == Some(self.n)),
            None => result.1 == Some(self.n),
        }
    )]
    #[ensures(self.n == 0usize ==> result == (0usize, Some(0usize)))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.n == 0 {
            return (0, Some(0));
        }

        let (lower, upper) = self.iter.size_hint();

        let lower = std::cmp::min(lower, self.n);

        let upper = match upper {
            Some(x) if x < self.n => Some(x),
            _ => Some(self.n),
        };

        (lower, upper)
    }
}

impl<I: ExactSizeIterator> ExactSizeIterator for Take<I> {
    #[logic(law)]
    #[ensures(forall<r> Self::size_hint.postcondition((&self,), r) ==> r.1 == Some(r.0))]
    fn size_is_exact(self) {
        self.iter.size_is_exact()
    }
}
