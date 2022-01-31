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
