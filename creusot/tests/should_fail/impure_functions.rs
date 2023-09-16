extern crate creusot_contracts;
use creusot_contracts::{logic::*, *};

#[ghost]
fn x<T>(v: &Vec<T>) -> Int {
    pearlite! { v.len()@ }
}

fn y() {
    let _ = x(&Vec::<()>::new());
}
