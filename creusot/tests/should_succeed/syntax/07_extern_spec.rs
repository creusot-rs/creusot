extern crate creusot_contracts;
use creusot_contracts::*;

fn main() {
    // An extern spec defined in `creusot_contracts`
    let v: Vec<bool> = Vec::new();
}

fn has_params<V, U, X>(a: V, b: U, c: X) {}

extern_spec! {
    fn has_params<V,U,X>(a: V, b: U, c: X)
}

trait A {}

trait B: A {}

fn uses_a<T: A>(x: T) {}

extern_spec! {
    fn uses_a<T : B>(x : T)
}

fn client<T: B>(y: T) {
    uses_a(y)
}

fn renamed_params<A, B, C>(a: A, b: B, c: C) {}

#[logic]
fn id<T>(x: T) -> T {
    x
}
