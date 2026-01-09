extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p.0@ == 1)]
#[ensures(result@ == 2)]
pub fn disjoint_captures(mut p: (i32, i32)) -> i32 {
    let p0 = &p.0;
    let mut clos = #[ensures(p.1@ == 1)]
    || {
        p.1 = 1;
    };
    clos();
    *p0 + p.1
}
