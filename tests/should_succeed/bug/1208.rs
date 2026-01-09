extern crate creusot_std;
use creusot_std::prelude::*;

pub enum Q {
    Zero,
    Frac1(Int),
}
use Q::*;

impl Invariant for Q {
    #[logic(open)]
    fn invariant(self) -> bool {
        true
    }
}

impl Q {
    #[logic(open)]
    #[ensures(result.invariant())]
    pub fn mul(self, y: Q) -> Q {
        match (self, y) {
            (Zero, _) => Zero,
            (_, Zero) => Zero,
            (Frac1(n), Frac1(m)) => Frac1(n + m),
        }
    }
}
