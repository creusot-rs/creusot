use crate::{trusted, Int};

#[trusted]
pub trait WellFounded {}

// FIXME: Int is NOT well-founded. But this is required for induction over integers
#[trusted]
impl WellFounded for Int {}

#[trusted]
impl WellFounded for u8 {}
#[trusted]
impl WellFounded for u16 {}
#[trusted]
impl WellFounded for u32 {}
#[trusted]
impl WellFounded for u64 {}
#[trusted]
impl WellFounded for u128 {}
#[trusted]
impl WellFounded for usize {}

#[trusted]
impl WellFounded for i8 {}
#[trusted]
impl WellFounded for i16 {}
#[trusted]
impl WellFounded for i32 {}
#[trusted]
impl WellFounded for i64 {}
#[trusted]
impl WellFounded for i128 {}
#[trusted]
impl WellFounded for isize {}

#[trusted]
impl<T: WellFounded> WellFounded for &T {}

#[trusted]
impl<T: WellFounded> WellFounded for &mut T {}
