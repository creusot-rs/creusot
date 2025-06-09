extern crate creusot_contracts;

use creusot_contracts::*;

#[open(self)]
#[logic(prophetic)]
#[requires((*x)@ == 1 && (^x)@ == 2)]
#[ensures(result == -1)]
fn bor_1_2(x: &mut i32) -> Int {
    pearlite! { (*x)@ - (^x)@ }
}

#[open(self)]
#[logic(prophetic)]
#[requires((*x)[2].0@ == 1)]
#[requires((^x)[2].0@ == 2)]
#[ensures(result)]
pub fn f(x: &mut [(i32, i32); 5]) -> bool {
    bor_1_2(&mut (*x)[2].0) == -1
}

#[open(self)]
#[logic]
#[requires(0 <= x && x < 2)]
pub fn bool_of_int(x: Int) -> bool {
    if x == 0 { true } else { false }
}

#[open(self)]
#[logic]
#[requires(0 <= x && x < 2)]
#[ensures(result)]
pub fn g(x: Int) -> bool {
    let map = |x| if 0 <= x && x < 2 { bool_of_int(1 - x) } else { true };
    map.get(x) || map.get(1 - x)
}
