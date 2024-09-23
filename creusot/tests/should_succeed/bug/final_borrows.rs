extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result == r)]
pub fn reborrow_id<T>(r: &mut T) -> &mut T {
    r
}

#[ensures(if b { result == r1 } else { result == r2 })]
pub fn select<'a, T>(b: bool, r1: &'a mut T, r2: &'a mut T) -> &'a mut T {
    if b {
        r1
    } else {
        r2
    }
}

#[ensures(result == &mut r.0)]
pub fn reborrow_field<T>(r: &mut (T, T)) -> &mut T {
    &mut r.0
}

#[ensures(result == &mut r.0.1)]
pub fn nested_fields<T>(r: &mut ((T, T), T)) -> &mut T {
    let borrow1 = &mut r.0;
    &mut borrow1.1
}

#[ensures(result == &mut (*x.0).1)]
pub fn really_nested_fields<T>(x: (&mut (T, T), T)) -> &mut T {
    let borrow = &mut (*x.0).1;
    borrow
}

#[ensures(match x.0 {
    None => result == &mut x.1,
    Some(_) => exists<r: &mut T> result == r && (*x).0 == Some(*r) && (^x).0 == Some(^r)
})]
pub fn select_field<T>(x: &mut (Option<T>, T)) -> &mut T {
    match &mut x.0 {
        None => {}
        Some(r) => return r,
    }
    &mut x.1
}

#[ensures((^r)@ == 7)]
fn set_7(r: &mut i32) {
    *r = 7;
}

#[ensures(result@ == 9)]
pub fn not_final_borrow_works() -> i32 {
    let mut x = 1i32;
    let r = &mut x;
    let r1 = &mut *r;
    set_7(r1);
    let y = *r;
    *r = 2;
    return x + y;
}

#[ensures(result@ == 3)]
pub fn branching(b: bool) -> i32 {
    let mut x = 3;
    let mut y;
    let mut r1 = &mut x;
    // r2 is not a final reborrow
    let r2 = &mut *r1;
    y = *r2;
    if b {
        // kill r1
        r1 = &mut y;
        y = *r1;
    } else {
        // gen  r1
        let r2 = &mut *r1;
        y = *r2;
    }
    y
}

#[ensures(*result == **x)]
#[ensures(^result == *^x)]
pub fn unnesting_non_extensional<'a: 'b, 'b, T>(x: &'a mut &'b mut T) -> &'b mut T {
    &mut **x
}

//=============================
//=========== BOXES ===========
//=============================

#[ensures(result == *x)]
pub fn box_deref<T>(x: Box<T>) -> T {
    *x
}

#[ensures(true)]
pub fn box_reborrow_direct<T>(mut x: Box<T>) {
    let borrow: &mut T = &mut *x;
    proof_assert! {
        *borrow == *x
    }
}

#[ensures(result == (**x))]
pub fn box_reborrow_indirect<T: Copy>(x: &mut Box<T>) -> T {
    let borrow: &mut T = &mut **x;
    *borrow
}

#[requires((**((*x).1))@ == 3)]
#[ensures(result@ == 3)]
pub fn box_reborrow_in_struct(x: &mut (i32, &mut Box<i32>)) -> i32 {
    let borrow: &mut i32 = &mut **x.1;
    *borrow
}

#[ensures(result == *x)]
pub fn borrow_in_box<T>(x: Box<&mut T>) -> &mut T {
    &mut **x
}

#[requires((*(*x).1)@ == 2)]
#[ensures(result@ == 2)]
pub fn borrow_in_box_tuple_1(x: Box<(i32, &mut i32)>) -> i32 {
    let borrow: &mut i32 = &mut *(*x).1;
    *borrow
}

#[requires((*(*x.1))@ == 2)]
#[ensures(result@ == 2)]
pub fn borrow_in_box_tuple_2(x: (i32, Box<&mut i32>)) -> i32 {
    let borrow: &mut i32 = &mut *(*x.1);
    *borrow
}

#[ensures(result == &mut **x)]
pub fn reborrow_in_box<T>(x: &mut Box<T>) -> &mut T {
    &mut **x
}

//=========================================
//=========== NON-MUTATING USES ===========
//=========================================

// This checks that various mir non-mutating instructions preserve the final borrow property

// Non-mutating uses not featured here:
// - 'Copy': cannot be emitted for a mutable borrow
// - 'Projection': cannot appear in the analysis
// - 'AddressOf': not supported by Creusot

pub fn shared_borrow_no_gen<T>(bor: &mut T) {
    let b1 = &mut *bor;
    let _shared = &bor;
    proof_assert!(b1 == bor);
}

pub fn inspect_no_gen<T>(x: &mut Option<T>) {
    let r = &mut *x;

    if matches!(x, Some(_)) {
        return;
    }
    proof_assert!(r == x);
}

pub fn place_mention_no_gen<T>(x: &mut Option<T>) {
    let _r = &mut *x;
    let _ = x;
    proof_assert!(_r == x);
}

pub fn shallow_borrow_no_gen(x: &mut Option<i32>) {
    let _r = &mut *x;
    // x / *x is shallow borrowed here
    match x {
        Some(ref inner) if *inner == 2 => {
            proof_assert!(_r == x);
        }
        _ => {}
    }
}

//=============================
//=========== SLICE ===========
//=============================

#[requires(v@.len() == 42)]
#[ensures(result == &mut v[12])]
pub fn index_mut_slice<T>(v: &mut [T]) -> &mut T {
    &mut v[12]
}

#[requires(v@.len() == 31)] // FIXME
#[ensures(result == &mut v[12usize])]
pub fn index_mut_array<T>(v: &mut [T; 31]) -> &mut T {
    &mut v[12]
}
