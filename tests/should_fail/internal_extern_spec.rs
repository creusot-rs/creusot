extern crate creusot_std;
use creusot_std::prelude::*;

extern_spec! {
    impl<T: Clone + Copy> Clone for Seq<T> {
        #[requires(false)]
        fn clone(&self) -> Self;
    }
}
