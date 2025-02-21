extern crate creusot_contracts;

enum Option<T> {
    Some(T),
    None,
}
use Option::*;

fn inexhaustive_match(x: Option<()>) {
    match x {
        None => (),
    }
}
