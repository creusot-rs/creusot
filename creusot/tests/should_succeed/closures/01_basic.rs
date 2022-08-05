extern crate creusot_contracts;

pub fn uses_closure() {
    let y = true;
    let _x = (|| y)();
}

pub fn multi_arg() {
    let x = |a, b| a + b;
    let _a = (x)(0, 3);
}

// fn generic_closure<T>(x: T) -> T{
//   (|| { x })()
// }

// fn call_closure() {
//   closure_param(|x : u32| { () })
// }
