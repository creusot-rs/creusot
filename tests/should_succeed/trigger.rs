extern crate creusot_std;

use creusot_std::prelude::*;

mod inner {
    use creusot_std::prelude::*;

    #[logic(open(self))]
    pub fn id(i: Int) -> Int {
        i
    }

    #[logic(open(self))]
    #[ensures(forall<i, j> #[trigger(id(i), id(j))] i <= j ==> id(i) <= id(j))]
    pub fn id_mono() {}
}
use inner::*;

#[ensures(id(5) >= id(2))]
pub fn test() {
    snapshot!(id_mono);
}
