#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
extern crate creusot_contracts;
use creusot_contracts::*;

struct Seven();

impl Model for Seven {
    type Model = Int;
    logic! {
        #[trusted]
        fn model(self) -> Self::Model {
            panic!()
        }
    }
}

#[trusted]
#[ensures(@result === 7)]
fn seven() -> Seven {
    Seven()
}

struct Pair<T, U>(T, U);

impl<T, U> Model for Pair<T, U> {
    type Model = (T, U);
    logic! {
        #[trusted]
        fn model(self) ->Self::Model  {
            panic!()
        }
    }
}

#[trusted]
#[ensures(@result === (a, b))]
fn pair<T, U>(a: T, b: U) -> Pair<T, U> {
    Pair(a, b)
}
