extern crate creusot_contracts;
use creusot_contracts::*;

// Fails because its already defined in `creusot-contracts`
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

fn main() {
    let _: Vec<bool> = Vec::new();
}
