extern crate creusot_contracts;
use creusot_contracts::*;

#[logic(open)]
pub fn test_logic((x, _): (u32, u32)) -> u32 {
    x
}

#[ensures(result == x)]
pub fn test_program((x, _): (u32, u32)) -> u32 {
    x
}

pub fn test_closure() {
    let cl1 = #[ensures(result == b)]
    |_c, (_a, b)| b;
    let cl2 = #[ensures(result == b)]
    |(_a, b)| b;
    let _a = (cl1)(4, (0, 3));
    let _b = (cl2)((0, 4));
}

pub struct T(pub u32);

// #[ensures(result == x)]
// pub fn test_struct_pat(T(x): T) {
//     x
// } Fails due to different bug #605

impl T {
    #[ensures(result == x)]
    pub fn test_method(self, (x, _): (u32, u32)) -> u32 {
        x
    }
}
