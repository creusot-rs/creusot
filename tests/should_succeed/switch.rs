extern crate creusot_std;

pub enum Option<T> {
    Some(T),
    None,
}
use Option::*;

pub fn test(o: Option<u32>) -> bool {
    match o {
        Some(x) => x > 0,
        None => false,
    }
}

pub fn test2(o: (Option<u32>, u32)) -> u32 {
    match o.0 {
        Some(x) => x,
        None => o.1,
    }
}
