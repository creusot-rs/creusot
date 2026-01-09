extern crate creusot_std;
use creusot_std::prelude::*;

// Fails because its already defined in `creusot-std`
extern_spec! {
    mod std {
        mod vec {
            impl<T> Vec<T> {
                #[requires(true == true)]
                fn new() -> Vec<T>;
            }
        }
    }
}

pub fn main() {
    let _: Vec<bool> = Vec::new();
}
