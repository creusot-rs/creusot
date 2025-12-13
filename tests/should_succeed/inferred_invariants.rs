extern crate creusot_contracts;
use creusot_contracts::prelude::*;

fn f<T>(_: &mut T) {}

pub fn simple<T>(x: &mut T) {
    loop {
        f(x)
    }
}

pub fn swapper<'a, T>(mut x: &'a mut T, mut y: &'a mut T) {
    loop {
        let c = x;
        x = y;
        y = c;
    }
}

pub fn tuple<'a, T>(mut d: (&'a mut T, bool), mut e: (&'a mut T, bool)) {
    loop {
        let c = d;
        d = e;
        e = c;
    }
}

pub fn temp_move<'a, T>(mut x: &'a mut T) {
    loop {
        let c = x;
        x = c;
    }
}

pub fn y(v: &mut Vec<i32>) {
    let old_v = snapshot! { v };
    let mut i = 0;
    #[invariant(old_v@.len() == v@.len())]
    #[invariant(i@ <= 10)]
    loop {
        if i < v.len() {
            v[i] = 0;
        }

        i += 1;
        if i > 10 {
            break;
        }
    }
}

#[requires(*x == 0i32)]
#[ensures(^x == 0i32)]
pub fn nested_loops(x: &mut i32) {
    let mut i = 0;

    #[invariant(*x == 0i32)]
    loop {
        if i > 10 {
            break;
        }
        i += 1;

        let mut j = 0;

        #[invariant(*x == 0i32)]
        loop {
            if j > 10 {
                break;
            }
            j += 1;
            *x = 0;
        }
    }
}

#[requires(**x == 0i32)]
#[ensures(^x == y)]
#[ensures(^*x == 1i32)]
pub fn nested_borrows<'a, 'b>(x: &'a mut &'b mut i32, y: &'b mut i32) {
    let mut i = 0;

    #[invariant(**x == 0i32)]
    loop {
        if i > 10 {
            break;
        }
        i += 1;

        **x = 0;
    }

    let b = std::mem::replace(x, y);
    *b += 1;
}
