// WHY3PROVE Z3
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

// extern_spec! {
//     #[ensures(result === (@self_ === @rhs))]
//     fn std::cmp::PartialEq::eq<Self_, Rhs>(self_: &Self_, rhs: &Rhs) -> bool
//         where Self_ : PartialEq<Rhs>,
//               Self_ : Model,
//               Rhs: Model<ModelTy = Self_::ModelTy>,
// }

#[requires(@i < (@a).len())]
fn read_write<T: Eq + Copy + Model>(a: &mut Vec<T>, i: usize, x: T) {
    a[i] = x; // a is slice
    assert!(a[i] == x);
}
