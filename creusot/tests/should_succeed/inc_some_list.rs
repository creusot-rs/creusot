#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;
use creusot_contracts::*;

enum List {
    Cons(u32, Box<List>),
    Nil,
}
use List::*;
impl WellFounded for List {}

impl List {
    #[logic]
    fn sum(self) -> Int {
        match self {
            Cons(a, l) => Int::from(a) + l.sum(),
            Nil => 0,
        }
    }

    // TODO: Make this ghost
    #[pure]
    #[variant(*self)]
    #[ensures(self.sum() >= 0)]
    fn lemma_sum_nonneg(&self) {
        match self {
            Cons(_, l) => l.lemma_sum_nonneg(),
            Nil => (),
        }
    }

    #[requires(self.sum() <= 1_000_000)]
    #[ensures(Int::from(result) == self.sum())]
    fn sum_x(&self) -> u32 {
        match self {
            Cons(a, l) => *a + l.sum_x(),
            Nil => 0,
        }
    }

    #[ensures((^self).sum() - self.sum() == Int::from(^result) - Int::from(*result))]
    #[ensures(Int::from(*result) <= self.sum())]
    fn take_some(&mut self) -> &mut u32 {
        match self {
            Cons(ma, ml) => {
                ml.lemma_sum_nonneg();
                if rand::random() {
                    ma
                } else {
                    ml.take_some()
                }
            }
            Nil => loop {},
        }
    }
}

#[requires(l.sum() + Int::from(k) <= 1_000_000)]
fn inc_some_list(mut l: List, k: u32) {
    let sum0 = l.sum_x();
    let ma = l.take_some();
    *ma += k;
    assert!(l.sum_x() == sum0 + k);
}
