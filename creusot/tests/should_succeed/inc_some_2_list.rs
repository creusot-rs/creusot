extern crate creusot_contracts;
use creusot_contracts::*;

pub enum List {
    Cons(u32, Box<List>),
    Nil,
}
use List::*;

// FIXME: this should go away, we have not defined any order relation on List
#[trusted]
impl WellFounded for List {}

#[trusted]
fn random() -> bool {
    panic!()
}

impl List {
    #[logic]
    fn sum(self) -> Int {
        match self {
            Cons(a, l) => a.model() + l.sum(),
            Nil => 0,
        }
    }

    // TODO: Make this ghost
    #[logic]
    #[variant(*self)]
    #[ensures(self.sum() >= 0)]
    fn lemma_sum_nonneg(&self) {
        match self {
            Cons(_, l) => l.lemma_sum_nonneg(),
            Nil => (),
        }
    }

    #[requires(self.sum() <= 1_000_000)]
    #[ensures(@result == self.sum())]
    fn sum_x(&self) -> u32 {
        match self {
            Cons(a, l) => *a + l.sum_x(),
            Nil => 0,
        }
    }

    #[ensures((^self).sum() - self.sum() ==
        @^result.0 + (^result.1).sum() - @result.0 - (*result.1).sum())]
    #[ensures(@result.0 <= self.sum())]
    #[ensures(result.1.sum() <= self.sum())]
    fn take_some_rest(&mut self) -> (&mut u32, &mut List) {
        match self {
            Cons(ma, ml) => {
                ghost! { ml.lemma_sum_nonneg() };
                if random() {
                    (ma, ml)
                } else {
                    ml.take_some_rest()
                }
            }
            Nil => loop {},
        }
    }
}

#[requires(l.sum() + @j + @k <= 1_000_000)]
pub fn inc_some_2_list(mut l: List, j: u32, k: u32) {
    let sum0 = l.sum_x();
    let (ma, ml) = l.take_some_rest();
    let (mb, _) = ml.take_some_rest();
    *ma += j;
    *mb += k;
    assert!(l.sum_x() == sum0 + j + k);
}
