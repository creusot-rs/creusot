extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic(law)]
    fn la();

    #[logic]
    fn lo();
}

impl Tr for () {
    #[logic]
    fn la() {}

    #[logic(law)]
    fn lo() {}
}
