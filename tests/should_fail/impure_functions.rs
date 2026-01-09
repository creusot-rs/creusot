extern crate creusot_std;
use creusot_std::{logic::*, prelude::*};

#[logic]
fn x<T>(v: &Vec<T>) -> Int {
    pearlite! { v.len()@ }
}

pub fn y() {
    let _ = x(&Vec::<()>::new());
}
