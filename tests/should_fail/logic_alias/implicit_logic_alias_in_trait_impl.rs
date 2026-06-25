extern crate creusot_std;

use creusot_std::prelude::*;

pub trait T where
    Self: View<ViewTy = Int>,
{
    #[logic]
    fn is_zero_log(&self) -> bool {
        pearlite! {
            self@ == 0
        }
    }

    #[logic_alias(Self::is_zero_log)]
    fn is_zero(&self) -> bool;
}

impl T for i64 {
    fn is_zero(&self) -> bool {
        *self == 0
    }
}
