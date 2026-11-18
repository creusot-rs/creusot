use creusot_std::prelude::*;

#[conceal(recursive::cyclic)]
pub mod recursive {
    use super::*;

    #[logic]
    pub fn cyclic() {
        if true {
            cyclic();
        }
    }
}

#[conceal(recursive2::cyclic1)]
#[conceal(recursive2::cyclic2)]
pub mod recursive2 {
    use super::*;

    #[logic]
    pub fn cyclic1() {
        cyclic2();
    }

    #[logic]
    pub fn cyclic2() {
        cyclic1();
    }
}
