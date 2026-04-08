extern crate creusot_std;

pub fn f<T>(x: usize) {
    if x == 0 {
        f::<usize>(1)
    }
}
