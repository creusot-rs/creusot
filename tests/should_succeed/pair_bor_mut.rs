extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[ensures(if take_first { result == p.0 && ^p.1 == *p.1 }
          else { result == p.1 && ^p.0 == *p.0 } )]
pub fn pair_bor_mut<'a, T>(p: (&'a mut T, &'a mut T), take_first: bool) -> &'a mut T {
    if take_first { p.0 } else { p.1 }
}
