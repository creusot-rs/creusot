extern crate creusot_contracts;
use creusot_contracts::{logic::ra::Excl, resource::Resource, *};

#[ensures(x.id() != y.id())]
pub fn exclusivity(x: &Resource<Excl<i32>>, y: &Resource<Excl<i32>>) {
    if x.id_ghost() == y.id_ghost() {
        let _z = x.join_shared(y);
        assert!(false); // _z is invalid
    }
}
