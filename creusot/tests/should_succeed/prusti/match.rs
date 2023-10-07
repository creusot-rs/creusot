#![feature(never_type)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic]
pub fn test1<'a, X>(x: Result<&'a mut X, &'a mut X>) -> &'a mut X {
    match x {
        Ok(ok) => ok,
        Err(err) => err
    }
}

#[open]
#[logic]
pub fn test_cur<'a, X>(x: Result<&'a mut X, &mut X>) -> X {
    let r = match x {
        Ok(ok) => ok,
        Err(err) => err
    };
    *r
}

// #[after_expiry('a, *(if b {x} else {result}) == 5u32)]
// pub fn test_proc<'a>(x: &'a mut u32, b: bool) -> &'a mut u32 {
//     x
// }

#[requires(*(if b {x} else {y}) == 5u32)]
pub fn test_proc_cur<'a, 'b>(x: &'a mut u32, y: &'b mut u32, b: bool) {
    let r = if b {x} else {y};
    *r = 5;
}

#[open]
#[logic]
pub fn id<'a, X>(x: &'a mut X) -> &'a mut X {
    x
}

#[open]
#[logic]
#[requires(x != None)]
pub fn unwrap<'a, 'b>(x: Option<&'a mut u32>) -> &'a mut u32 {
    match x {
        Some(x) => x,
        None => id(absurd),
    }
}

#[requires({let x = match x {Ok(x) => x, Err(x) => x}; *(x.0) == 0u32})]
// #[ensures({let (a, b) = match x {Ok(x) => x, Err(x) => x}; *a == *b})]
pub fn test_never(x: Result<(&mut u32, &mut u32), !>)  {}