extern crate creusot_contracts;
use creusot_contracts::*;

fn omg() {
    let mut a = 0;

    (|| {
        a += 1;
        0
    })();
}
