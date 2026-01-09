extern crate creusot_std;

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
