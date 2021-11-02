pub trait WellFounded {}

impl WellFounded for u32 {}
impl WellFounded for u64 {}
impl WellFounded for i32 {}
impl WellFounded for i64 {}

impl<T: WellFounded> WellFounded for &T {}
