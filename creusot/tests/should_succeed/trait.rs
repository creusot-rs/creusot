// fn uses_ord<T : Ord>(t : T) -> bool {
// 	true
// }

trait TraitWParams<D, C> {}

fn uses_custom<A, B, T : TraitWParams<A, B>>(t : T) {}

trait TraitWParams2<D : Ord, C> : TraitWParams<D, C> {}

fn uses_custom2<A : Ord, B, T : TraitWParams2<A, B>>(t : T) {}


// trait Super {}

// trait Child : Super {}

// fn uses_super<T : Child>(t : T) {}


// trait ParamsSuper<A>
//   where A : Ord {}

// fn uses_params_super<T : ParamsSuper<u32>>(t : T) {}

// trait AssocType {
//   type T : Ord;
// }

// fn uses_assoc_type<T : AssocType>(t : T::T) {}

fn main () { }
