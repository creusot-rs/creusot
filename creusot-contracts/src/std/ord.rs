use crate as creusot_contracts;
use creusot_contracts_proc::*;

use crate::logic::ord::*;
pub use std::cmp::Ordering;

pub trait Ord: OrdLogic + Eq {
    #[ensures(result == self.cmp_log(*o))]
    fn cmp(&self, o: &Self) -> Ordering;

    #[ensures(result == (*self <= *o))]
    fn le(&self, o: &Self) -> bool {
        match self.cmp(o) {
            Ordering::Greater => false,
            _ => true,
        }
    }

    #[ensures(result == (*self >= *o))]
    fn ge(&self, o: &Self) -> bool {
        match self.cmp(o) {
            Ordering::Less => false,
            _ => true,
        }
    }

    #[ensures(result == (*self > *o))]
    fn gt(&self, o: &Self) -> bool {
        match self.cmp(o) {
            Ordering::Greater => true,
            _ => false,
        }
    }

    #[ensures(result == (*self < *o))]
    fn lt(&self, o: &Self) -> bool {
        match self.cmp(o) {
            Ordering::Less => true,
            _ => false,
        }
    }
}
