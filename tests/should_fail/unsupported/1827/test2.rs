use creusot_std::prelude::*;

#[logic]
fn is_zero(v: Option<Int>) -> Int {
    pearlite! {
        match v {
            Some(0) => 1,
            None    => 0,
        }
    }
}
