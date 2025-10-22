extern crate creusot_contracts;
use creusot_contracts::prelude::*;

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
