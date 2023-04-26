extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result == true)]
pub fn eq() -> bool {
    1.0 == 2.0
}

#[ensures(result == true)]
pub fn lt() -> bool {
    1.0 < 2.0
}

#[ensures(result == true)]
pub fn le() -> bool {
    1.0 <= 2.0
}

#[ensures(result == true)]
pub fn gt() -> bool {
    2.0 > 1.0
}

#[ensures(result == true)]
pub fn ge() -> bool {
    2.0 >= 1.0
}

#[ensures(result == true)]
pub fn neg() -> bool {
    -2.0 <= 1.0
}
