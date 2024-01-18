#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[requires(*(x.0) == 0u32)]
#[ensures({let (a, b) = x; *a == *b})]
pub fn test(x: (&mut u32, &mut u32)) {
    *(x.1) = *(x.0)
}

#[open]
#[logic]
pub fn test_constructor<'a, 'b>(x: &'a mut u32, y: &'b mut u32) -> (&'a mut u32, &'b mut u32) {
    (x, y)
}

pub struct SamePair<X>(X, X);

#[open]
#[logic]
pub fn test_constructor2<'a>(x: &'a mut u32, y: &'a mut u32) -> SamePair<&'a mut u32> {
    SamePair(x, y)
}

pub struct HasModel<T: ShallowModel>(T::ShallowModelTy);

#[open]
#[logic]
pub fn test_constructor3<T: ShallowModel>(x: T) -> HasModel<T> {
    HasModel(x.shallow_model())
}
