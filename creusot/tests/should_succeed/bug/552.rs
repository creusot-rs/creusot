extern crate creusot_contracts;
use creusot_contracts::{ensures, maintains, predicate, requires};

pub struct Transition;
pub struct Machine;

pub trait MachineTrait {
    #[predicate]
    fn invariants(self) -> bool;

    #[maintains((mut self).invariants())]
    fn step(&mut self) -> bool;
}

impl MachineTrait for Machine {
    #[predicate]
    fn invariants(self) -> bool {
        true
    }

    #[maintains((mut self).invariants())]
    fn step(&mut self) -> bool {
        self.transition(); // Comment out this line and it works
        false
    }
}

impl Machine {
    #[requires(self.invariants())]
    pub fn transition(&self) -> Transition {
        Transition
    }
}
