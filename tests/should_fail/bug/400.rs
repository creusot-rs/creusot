extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Tr {
    #[law]
    fn la();

    #[logic]
    fn lo();
}

impl Tr for () {
    #[logic]
    fn la() {}

    #[law]
    fn lo() {}
}
