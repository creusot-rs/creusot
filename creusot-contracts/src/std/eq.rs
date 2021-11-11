use crate as creusot_contracts;
use creusot_contracts_proc::*;

use crate::logic::*;

pub trait Eq: EqLogic {
    #[ensures(result === self.log_eq(*o))]
    fn eq(&self, o: &Self) -> bool;
}
