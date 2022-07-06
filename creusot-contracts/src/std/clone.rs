use crate as creusot_contracts;
use creusot_contracts_proc::*;

extern_spec! {
    mod std {
        mod clone {
            trait Clone {
                #[ensures(result == *self)]
                fn clone(&self) -> Self;
            }
        }
    }
}
