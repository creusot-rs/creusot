extern crate creusot_std;

pub enum E {
    A(u32),
}

// A tuple-variant constructor used as a function value, rather than applied
// directly, reaches Creusot as an item of kind `Ctor`, which it does not
// translate. Creusot must reject it with a diagnostic: asking rustc for the
// argument idents of the synthesized `{constructor#0}` item instead ICEs,
// as it did in 0.12.0 (creusot-rs/creusot#2223).
pub fn g(o: Option<u32>) -> Option<E> {
    o.map(E::A)
}
