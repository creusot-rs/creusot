extern crate creusot_std;
use creusot_std::prelude::*;

pub trait BadLaw {
    #[logic(law)]
    fn my_law<T>(x: T);
}

impl BadLaw for () {
    fn my_law<T>(_: T) {}
}
