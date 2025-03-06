extern crate creusot_contracts;

// Broken because of trait generics
pub trait A {
    fn from_b<B>(x: Self) -> B;
}

pub fn uses_generic<T: A>(b: T) -> u32 {
    A::from_b(b)
}
