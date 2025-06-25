extern crate creusot_contracts;

// fn uses_ord<T: Ord>(t: T) -> bool {
// 	true
// }

pub trait TraitWParams<D, C> {}

pub fn uses_custom<A, B, T: TraitWParams<A, B>>(_t: T) {}

pub trait TraitWParams2<D: Ord, C>: TraitWParams<D, C> {}

pub fn uses_custom2<A: Ord, B, T: TraitWParams2<A, B>>(_t: T) {}

// trait Super {}

// trait Child: Super {}

// fn uses_super<T: Child>(t: T) {}

// trait ParamsSuper<A>
//   where A: Ord {}

// fn uses_params_super<T: ParamsSuper<u32>>(t: T) {}

// trait AssocType {
//   type T: Ord;
// }

// fn uses_assoc_type<T: AssocType>(t: T::T) {}
