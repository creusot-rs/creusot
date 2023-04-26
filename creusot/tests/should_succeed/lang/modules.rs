#![feature(min_specialization)]
extern crate creusot_contracts;

pub mod nested {
    use creusot_contracts::*;

    enum Nested {
        Test,
    }

    #[trusted]
    impl Resolve for Nested {
        #[predicate]
        fn resolve(self) -> bool {
            true
        }
    }

    #[ensures(result == true)]
    pub fn inner_func() -> bool {
        let _ = Nested::Test;
        true
    }

    pub mod further {
        pub fn another() -> bool {
            false
        }
    }
}

pub fn f() {
    nested::inner_func();
    use nested::further::*;
    another();
}
