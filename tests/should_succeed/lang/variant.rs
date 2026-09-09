extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[variant(x@)]
pub fn frec(x: usize) {
    if x != 0 {
        frec(x - 1)
    }
}

#[check(terminates)]
#[requires(|mode| mode.terminates() ==> x@ >= 1)]
#[variant(x@)]
pub fn frec_partial(x: usize) {
    if x == 0 {
        frec_partial(x)
    } else if x > 1 {
        frec_partial(x - 1)
    }
}

#[check(terminates)]
pub fn gloop(x: usize) {
    ghost! {
      let mut i = x;
      #[variant(i@)]
      while i > 0 {
        i -= 1;
      }
    };
    let mut i = x;
    #[variant(i@)]
    while i > 0 {
        i -= 1;
    }
}

#[check(terminates)]
#[requires(|mode| mode.terminates() ==> x@ >= 1)]
pub fn gloop_partial(x: usize) {
    let mut i = x;
    #[invariant(|mode| mode.terminates() ==> i@ >= 1)]
    #[variant(i@)]
    loop {
        if i == 0 {
            continue;
        }
        if i == 1 {
            break;
        }
        i -= 1;
    }
}
