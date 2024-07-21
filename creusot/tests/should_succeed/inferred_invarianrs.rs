extern crate creusot_contracts;
use creusot_contracts::*;

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
