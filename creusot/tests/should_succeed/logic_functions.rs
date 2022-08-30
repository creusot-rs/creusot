extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
fn logic() -> bool {
    true
}

#[ensures(logic())]
pub fn use_logic() {}

// When we want to use pearlite syntax, we use pearlite! macro
#[logic]
fn logic_pearlite() -> bool {
    pearlite! { 0 == 0 }
}

#[ensures(logic_pearlite())]
pub fn use_logic_pearlite() {}

pub mod nested {
    use creusot_contracts::*;

    #[logic]
    pub fn nested() -> bool {
        true
    }
}

#[logic]
pub fn arith(n: Int, b: bool) -> Int {
    if !b {
        -n + n - n * n
    } else {
        n
    }
}

#[logic]
pub fn deref_pat<'a>(o: &'a Option<Int>) -> Int {
    match o {
        Some(a) => *a,
        None => 0,
    }
}
