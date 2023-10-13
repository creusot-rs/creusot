//  - cargo creusot -- --features=contracts    # for proofs with why3-ide.
extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

fn main() {
    let mut x = 0u32;
    let mut f = #[requires(x@ <= 100)]
    #[ensures(x@==old(x)@+1)]
    || {
        x += 1;
    };
    let mut g = || {
        f();
    };
    g();
    // dbg!(x);
}
