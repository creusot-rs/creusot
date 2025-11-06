use creusot_contracts::prelude::*;

#[logic]
pub fn has_zero(v: Option<(Option<Int>, Option<Int>)>) -> Int {
    pearlite! {
        match v {
            Some((Some(0), _)) | Some((_, Some(0))) => 1,
            _ => 0
        }
    }
}

