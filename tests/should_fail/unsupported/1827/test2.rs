use creusot_contracts::prelude::*;

#[logic]
fn is_zero(v: Option<Int>) -> Int {
    pearlite! {
        match v {
            Some(0) => 1,
            None    => 0,
        }
    }
}

