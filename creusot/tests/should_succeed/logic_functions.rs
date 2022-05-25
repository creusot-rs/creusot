extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
fn logic() -> bool {
    true
}

#[ensures(logic())]
fn use_logic() {}

// When we want to use pearlite syntax, we use pearlite! macro
#[logic]
fn logic_pearlite() -> bool {
    pearlite! { 0 == 0 }
}

#[ensures(logic_pearlite())]
fn use_logic_pearlite() {}

mod nested {
    use creusot_contracts::*;

    #[logic]
    fn nested() -> bool {
        true
    }
}

#[logic]
fn arith(n: Int, b: bool) -> Int {
    if !b {
        -n + n - n * n
    } else {
        n
    }
}

#[logic]
fn deref_pat<'a>(o: &'a Option<Int>) -> Int {
    match o {
        Some(a) => *a,
        None => 0,
    }
}
