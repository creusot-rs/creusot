extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(indirect)]
pub fn indirect() -> Int {
    3
}

#[logic(#[trigger(x + 1)] indirect)]
pub fn indirect_trig(x: Int) -> Int {
    x
}

#[logic]
#[ensures(result == 9)]
pub fn use_indirect() -> Int {
    indirect()
        + indirect_trig(0)
        + <() as Trait>::indirect()
        + <() as Trait>::indirect_trig(0)
        + <() as Trait>::decl(())
}

pub trait Trait {
    #[logic(indirect)]
    fn indirect() -> Int {
        3
    }

    #[logic(#[trigger(x + 1)] indirect)]
    fn indirect_trig(x: Int) -> Int {
        x
    }

    #[logic]
    fn decl(self) -> Int;
}

impl Trait for () {
    #[logic(#[trigger(self)]indirect)]
    fn decl(self) -> Int {
        3
    }
}
