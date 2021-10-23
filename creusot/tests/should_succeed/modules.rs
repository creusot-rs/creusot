extern crate creusot_contracts;

pub mod nested {
    use creusot_contracts::*;

    enum Nested {
        Test,
    }

    unsafe impl Resolve for Nested {
        #[predicate]
        fn resolve(self) -> bool {
            true
        }
    }

    #[ensures(result == true)]
    pub fn inner_func() -> bool {
        Nested::Test;
        true
    }

    pub mod further {
        pub fn another() -> bool {
            false
        }
    }
}

fn main() {
    nested::inner_func();
    use nested::further::*;
    another();
}
