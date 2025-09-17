extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

#[logic]
pub fn logic() -> bool {
    true
}

#[ensures(logic())]
pub fn use_logic() {}

// When we want to use pearlite syntax, we use pearlite! macro
#[logic]
pub fn logic_pearlite() -> bool {
    pearlite! { 0 == 0 }
}

#[ensures(logic_pearlite())]
pub fn use_logic_pearlite() {}

pub mod nested {
    use creusot_contracts::*;

    #[logic(open)]
    pub fn nested() -> bool {
        true
    }
}

#[logic(open)]
pub fn arith(n: Int, b: bool) -> Int {
    if !b { -n + n - n * n } else { n }
}

#[logic(open)]
pub fn deref_pat<'a>(o: &'a Option<Int>) -> Int {
    match o {
        Some(a) => *a,
        None => 0,
    }
}

#[logic(open)]
#[creusot::why3_meta("rewrite_def", function, self)]
pub fn quatorze() -> Int {
    14
}

#[ensures(quatorze() == 14)]
pub fn use_quatorze() {}
