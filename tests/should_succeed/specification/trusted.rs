extern crate creusot_contracts;

use creusot_contracts::*;

#[trusted]
pub fn call_external() {
    println!("Hello world!");
}

#[trusted]
#[ensures(result == 10u32)]
pub fn lie() -> u32 {
    5 // I'm evil
}

#[ensures(result == 10u32)]
pub fn victim_of_lie() -> u32 {
    lie()
}

#[predicate]
#[trusted]
#[open]
pub fn trusted_pred(_x: u32) -> bool {
    true
}

#[ensures(result == 10u32)]
pub fn innocent_victim() -> u32 {
    foo::my_unverified_code();
    foo::another_module::im_out_of_control()
}

#[trusted]
mod foo {
    use creusot_contracts::*;
    #[ensures(false)]
    pub fn my_unverified_code() -> u32 {
        0
    }

    pub mod another_module {
        use creusot_contracts::*;
        #[ensures(false)]
        pub fn im_out_of_control() -> u32 {
            5
        }
    }
}
