extern crate creusot_std;
use creusot_std::invariant::Guarded;

pub fn f(g: Guarded<&mut i32>) -> &mut i32 {
    let b = g.inner;
    b
}
