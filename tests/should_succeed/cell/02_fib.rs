extern crate creusot_contracts;

use creusot_contracts::{predcell::PredCell, *};

#[logic]
#[open]
#[variant(i)]
pub fn fib(i: Int) -> Int {
    if i <= 0 {
        0
    } else if i == 1 {
        1
    } else {
        fib(i - 1) + fib(i - 2)
    }
}

#[open]
#[logic]
#[requires(0 <= i)]
#[ensures(fib(i) <= i.pow2())]
#[variant(i)]
pub fn lemma_fib_bound(i: Int) {
    if i == 0 {
        ()
    } else if i == 1 {
        ()
    } else {
        lemma_fib_bound(i - 2);
        lemma_fib_bound(i - 1)
    }
}

pub struct FibCache(pub Vec<PredCell<Option<usize>>>);

impl Invariant for FibCache {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! {
            forall<i: Int>
                0 <= i && i < self.0@.len() ==>
                forall<x: Option<usize>>
                    self.0@[i]@[x] == match x {
                        None => true,
                        Some(v) => v@ == fib(i)
                    }
        }
    }
}

#[requires(i@ < mem.0@.len())]
#[ensures(result@ == fib(i@))]
#[requires(i@ <= 63)]
pub fn fib_memo(mem: &FibCache, i: usize) -> usize {
    match mem.0[i].get() {
        Some(v) => v,
        None => {
            let fib_i = if i == 0 {
                0
            } else if i == 1 {
                1
            } else {
                snapshot! { lemma_fib_bound };
                fib_memo(mem, i - 1) + fib_memo(mem, i - 2)
            };
            proof_assert! { fib_i@ == fib(i@) };
            mem.0[i].set(Some(fib_i));
            fib_i
        }
    }
}
