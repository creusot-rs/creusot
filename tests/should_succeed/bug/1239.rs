extern crate creusot_contracts;
use creusot_contracts::*;

// The WP transformation by `vcgen.rs` put the pair constructor
// under the scope of the inner `let`, which caused accidental capture when we
// were using strings as variables.
#[open]
#[logic]
#[ensures(result == (1, 2))]
pub fn f() -> (Int, Int) {
    let x = 2;
    (
        {
            let x = 1;
            x
        },
        x,
    )
}
