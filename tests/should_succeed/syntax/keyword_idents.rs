// Rust identifiers that are Coma keywords must be renamed in the generated code.
extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Keywords {
    pub then: u64,
    pub theory: u64,
    pub so: u64,
    pub begin: u64,
    pub downto: u64,
    pub partial: u64,
    pub pure: u64,
    pub raises: u64,
}

#[logic(open)]
pub fn sum(k: Keywords) -> Int {
    pearlite! {
        match k {
            Keywords { then, theory, so, begin, downto, partial, pure, raises } =>
                then@ + theory@ + so@ + begin@ + downto@ + partial@ + pure@ + raises@
        }
    }
}

#[ensures(result@ == k.then@ && sum(k) >= result@)]
pub fn then(k: Keywords) -> u64 {
    let then = k.then;
    then
}
