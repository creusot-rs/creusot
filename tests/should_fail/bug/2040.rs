extern crate creusot_std;

pub fn f<T: Eq>(x: T) -> bool {
    x == x
}
