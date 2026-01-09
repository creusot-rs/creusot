extern crate creusot_std;
use creusot_std::prelude::*;

/// Attaching invariants to loops that don't loop
pub fn main() {
    let mut x = 0;

    #[invariant(x == 0usize)]
    while x == 0 {
        x = 1;
        break;
    }

    #[invariant(x == 1usize)]
    while let true = x == 1 {
        x = 2;
        break;
    }

    // Make sure to disable the `irrefutable_let_pattern` warning
    // for when the desugared else branch is unreachable.
    #[invariant(true)]
    while let () = () {
        break;
    }

    // Don't attach the invariant to the inner loop
    // (this is a regression test to remember that we used to
    // scan for loop headers innerwards instead of outwards)
    #[invariant(x == 2usize)]
    loop {
        while x != 3 {
            x = 3;
        }
        break;
    }

    // Don't attach the inner invariant to the outer loop
    #[invariant(x <= 4usize)]
    while x < 4 {
        #[invariant(x <= 3usize)]
        loop {
            break;
        }
        x = 4;
        assert!(x == 4)
    }

    // an inner loop in the condition!
    #[invariant (x == 4usize)]
    while {
        while x != 5 {
            x = 5
        }
        true
    } {
        break;
    }

    #[invariant(x == 5usize)]
    for _ in 0..10 {
        break;
    }
}
