extern crate creusot_contracts;
use creusot_contracts::*;

mod common;
pub use common::Iterator;

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
}
