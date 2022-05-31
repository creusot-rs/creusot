extern crate creusot_contracts;

pub fn uses_closure() {
    let y = true;
    let _x = (|| y)();
}

// fn generic_closure<T>(x: T) -> T{
//   (|| { x })()
// }

// fn call_closure() {
//   closure_param(|x : u32| { () })
// }
