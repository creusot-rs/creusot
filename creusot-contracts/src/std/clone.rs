use crate::macros::*;

extern_spec! {
    mod std {
        mod clone {
            trait Clone {
                // TODO:
                // Requiring result == *self seems too strong since objects can
                // contain information which is lost by the clone (e.g., capacity of
                // vectors...).
                #[ensures(result == *self)]
                fn clone(&self) -> Self;
            }
        }
    }
}
