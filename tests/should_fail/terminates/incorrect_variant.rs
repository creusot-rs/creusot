// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::*;

#[check(terminates)]
#[variant(x)]
pub fn incorrect_recursion(x: i32) {
    if x < -10 || x > 10 {
    } else if x % 2 == 0 {
        incorrect_recursion(x + 1)
    } else {
        incorrect_recursion(x - 1)
    }
}

#[logic]
#[variant(x)]
#[ensures(result == 0)]
pub fn incorrect_recursion_logic(x: Int) -> Int {
    if x == 0 {
        0
    } else if x % 2 == 0 {
        incorrect_recursion_logic(x + 1)
    } else {
        incorrect_recursion_logic(x - 1)
    }
}

#[check(terminates)]
pub fn incorrect_loop_variant(mut x: i32) {
    #[variant(x)]
    while x >= -10 && x <= 10 {
        if x % 2 == 0 { x += 1 } else { x -= 1 }
    }
}
