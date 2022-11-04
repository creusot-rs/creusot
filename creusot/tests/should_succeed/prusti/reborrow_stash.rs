#![allow(unused)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

struct Test{x: u32}

impl Test {
    #[ensures(*stash == old(self.x))]
    #[ensures(*result == old(self.x))]
    #[after_expiry(self.x == *result)]
    fn test(&mut self, stash: &mut u32) -> &mut u32 {
        *stash = self.x;
        &mut self.x
    }
}