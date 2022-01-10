extern crate creusot_contracts;
use creusot_contracts::*;

extern_spec! {
    #[requires(true === true)]
    fn std::vec::Vec::new<T>() -> Vec<T>
}

fn main() {
    let v: Vec<bool> = Vec::new();
}
