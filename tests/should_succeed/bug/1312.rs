extern crate creusot_std;

pub fn foo99() -> impl Fn(Option<i32>) -> i32 {
    let _my_closure = |x: Option<i32>| match x {
        Some(y) => y,
        None => unreachable!("unwrapped None"),
    };
    _my_closure
}
