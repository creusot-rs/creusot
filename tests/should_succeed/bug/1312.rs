extern crate creusot_contracts;

pub fn foo99() {
    let _my_closure = |x: Option<i32>| match x {
        Some(y) => y,
        None => unreachable!("unwrapped None"),
    };
}
