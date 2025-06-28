extern crate creusot_contracts;
use creusot_contracts::{logic::ra::Excl, resource::Resource, *};

#[ensures(x.id() != y.id())]
#[ensures(*x == ^x)]
pub fn exclusivity(x: &mut Resource<Excl<i32>>, y: &Resource<Excl<i32>>) {
    if x.id_ghost() == y.id_ghost() {
        x.valid_shared(y);
        assert!(false); // x * y cannot be valid
    }
}
