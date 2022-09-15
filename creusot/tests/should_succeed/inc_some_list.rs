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

    #[ensures((^self).sum() - self.sum() == @^result - @result)]
    #[ensures(@result <= self.sum())]
    fn take_some(&mut self) -> &mut u32 {
        match self {
            Cons(ma, ml) => {
                ghost! { ml.lemma_sum_nonneg() };
                if random() {
                    ma
                } else {
                    ml.take_some()
                }
            }
            Nil => loop {},
        }
    }
}

#[requires(l.sum() + @k <= 1_000_000)]
pub fn inc_some_list(mut l: List, k: u32) {
    let sum0 = l.sum_x();
    let ma = l.take_some();
    *ma += k;
    assert!(l.sum_x() == sum0 + k);
}
