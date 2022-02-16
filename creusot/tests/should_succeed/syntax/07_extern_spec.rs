extern crate creusot_contracts;
use creusot_contracts::*;

extern_spec! {
    #[requires(true === true)]
    fn std::vec::Vec::new<T>() -> Vec<T>
}

fn main() {
    let v: Vec<bool> = Vec::new();
}

fn has_params<V, U, X>(a: V, b: U, c: X) {}

extern_spec! {
    fn has_params<C,B,A>(a: A, b: B, c: C)
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

extern_spec! {
    #[ensures(id(d) === d)]
    fn renamed_params<T,U,V>(d: T, e: U, f: V)
}
