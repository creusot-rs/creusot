// NO_REPLAY

extern crate creusot_contracts;

fn generic_closure<A, B, F: Fn(A) -> B>(f: F, a: A) -> B {
    f(a)
}

pub fn mapper<A>(x: A) {
    let _ = generic_closure(|_a| (), x);
}
