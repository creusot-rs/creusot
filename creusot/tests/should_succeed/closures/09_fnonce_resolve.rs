extern crate creusot_contracts;
use creusot_contracts::*;

pub fn f(c: bool) {
    let mut x = 1i32;
    let mut y = 1i32;
    let bx = Box::new(&mut x);
    let by = Box::new(Box::new(&mut y));
    let f = #[requires((**bx)@ == 1 && (***by)@ == 1)]
    #[ensures((^*bx)@ + (^**by)@ == 3)]
    move || {
        if c {
            // TODO : fix #1072 and remove comments
            //proof_assert!((^**by)@ == 1);
            let bx2 = bx;
            **bx2 += 1;
            //proof_assert!((^*bx2)@ == 2);
        } else {
            // TODO : fix #1072 and remove comments
            //proof_assert!((^*bx)@ == 1);
            let by2 = by;
            ***by2 += 1;
            //proof_assert!((^**by2)@ == 2);
        }
    };
    f();
    proof_assert!(x@+y@ == 3);
}
