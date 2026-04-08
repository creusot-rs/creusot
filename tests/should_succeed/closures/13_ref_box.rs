extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
fn call_fn<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| exists<f2> f.postcondition_mut(mode, (x,), f2, result) && resolve(f2))]
fn call_fnmut<F: FnMut(i32) -> i32>(mut f: F, x: i32) -> i32 {
    f(x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition_once(mode, (x,), result))]
fn call_fnonce<F: FnOnce(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test1<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fn(&f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test2<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fn(Box::new(f), x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test3<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnmut(&f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test4<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnmut(Box::new(f), x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test5<F: Fn(i32) -> i32>(mut f: F, x: i32) -> i32 {
    call_fnmut(&mut f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test6<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnonce(&f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test7<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnonce(Box::new(f), x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test8<F: Fn(i32) -> i32>(mut f: F, x: i32) -> i32 {
    call_fnonce(&mut f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| exists<f2> f.postcondition_mut(mode, (x,), f2, result) && resolve(f2))]
pub fn test9<F: FnMut(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnmut(Box::new(f), x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| exists<f2> f.postcondition_mut(mode, (x,), f2, result) && resolve(f2))]
pub fn test10<F: FnMut(i32) -> i32>(mut f: F, x: i32) -> i32 {
    call_fnmut(&mut f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| exists<f2> f.postcondition_mut(mode, (x,), f2, result) && resolve(f2))]
pub fn test11<F: FnMut(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnonce(Box::new(f), x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| exists<f2> f.postcondition_mut(mode, (x,), f2, result) && resolve(f2))]
pub fn test12<F: FnMut(i32) -> i32>(mut f: F, x: i32) -> i32 {
    call_fnonce(&mut f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition_once(mode, (x,), result))]
pub fn test13<F: FnMut(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnonce(Box::new(f), x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test14<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnmut(f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| f.postcondition(mode, (x,), result))]
pub fn test15<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnonce(f, x)
}

#[requires(|mode| f.precondition(mode, (x,)))]
#[ensures(|result, mode| exists<f2> f.postcondition_mut(mode, (x,), f2, result) && resolve(f2))]
pub fn test16<F: FnMut(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fnonce(f, x)
}
