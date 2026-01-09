extern crate creusot_std;
use creusot_std::prelude::*;

pub struct HasMutRef<'a, T>(pub &'a mut T);

#[ensures((^x.0)@ == 5)]
pub fn test(x: HasMutRef<'_, u32>) {
    *x.0 = 5
}
