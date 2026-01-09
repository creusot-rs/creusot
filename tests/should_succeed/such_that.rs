extern crate creusot_std;
use creusot_std::{logic::such_that, prelude::*};

pub fn foo() {
    let x = snapshot!(such_that(|x| x + 1 == 42));
    proof_assert!(*x == 41);

    let y = even();

    let mapping = snapshot!(|x: Int| x + y@);
    let predicate = snapshot!(|x: Int| mapping[x] + 1 == 0);
    proof_assert!(predicate[-y@ - 1]);
    let x = snapshot!(such_that(*predicate));
    proof_assert!(*x + y@ + 1 == 0);
}

#[ensures(result@ % 2 == 0)]
fn even() -> i32 {
    2
}
