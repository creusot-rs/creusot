extern crate creusot_contracts;
use creusot_contracts::*;

// Fails because its already defined in `creusot-contracts`
extern_spec! {
    #[requires(true == true)]
    fn std::vec::Vec::new<T>() -> Vec<T>
}

fn omg() {}

// fails because its defined twice in the current crate
extern_spec! {
    #[requires(true == true)]
    fn crate::omg() -> ()
}

mod a {
    use creusot_contracts::*;

    extern_spec! {
        #[requires(true == true)]
        fn crate::omg() -> ()
    }
}

fn main() {
    let _: Vec<bool> = Vec::new();
    omg();
}
