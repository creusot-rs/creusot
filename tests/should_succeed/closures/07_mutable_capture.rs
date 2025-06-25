extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(x@ == 100_000)]
pub fn test_fnmut(mut x: u32) {
    let mut c = {
        #[requires(x@ < 1_000_000)]
        #[ensures(x@ == old(x)@ + 1)]
        || {
            x += 1;
            5
        }
    };
    c();
    c();

    proof_assert! { x@ == 100_002};
}

#[requires(f.precondition(()))]
#[requires(forall<st1, r> f.postcondition_mut((), st1, r) ==> st1.precondition(()))]
#[ensures(exists<st1, st2, r>
    f.postcondition_mut((), st1, r) &&
    st1.postcondition_mut((), st2, result) &&
    resolve(&st2))]
fn call_fnmut<F: FnMut() -> i32>(mut f: F) -> i32 {
    f();
    f()
}

#[requires(f.precondition(()))]
#[ensures(f.postcondition_once((), result))]
fn call_fnonce<F: FnOnce() -> i32>(f: F) -> i32 {
    f()
}

#[requires(x@ == 100_000)]
pub fn test_fnmut2(mut x: u32) {
    let mut c = {
        #[requires(x@ < 1_000_000)]
        #[ensures(x@ == old(x)@ + 1)]
        || {
            x += 1;
            5
        }
    };
    call_fnmut(&mut c);
    call_fnmut(c);
    proof_assert! { x@ == 100_004 };
}

#[requires(x@ == 100_000)]
pub fn test_fnmut3(mut x: u32) {
    let mut c = || {
        x += 1;
        5
    };
    call_fnonce(&mut c);
    call_fnonce(c);
    proof_assert! { x@ == 100_002 };
}

#[requires(x@ == 100_000)]
pub fn test_fnmut2box(mut x: u32) {
    let mut c = {
        #[requires(x@ < 1_000_000)]
        #[ensures(x@ == old(x)@ + 1)]
        || {
            x += 1;
            5
        }
    };
    call_fnmut(Box::new(&mut c));
    call_fnmut(Box::new(Box::new(c)));
    proof_assert! { x@ == 100_004 };
}

#[requires(x@ == 100_000)]
pub fn test_fnmut3box(mut x: u32) {
    let mut c = || {
        x += 1;
        5
    };
    call_fnonce(&mut &mut c);
    call_fnonce(Box::new(Box::new(c)));
    proof_assert! { x@ == 100_002 };
}
