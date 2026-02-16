use crate::prelude::*;
use core::cmp::Ordering;

/// ↑V
#[opaque]
pub struct SyncView;

impl OrdLogic for SyncView {
    #[logic(opaque)]
    fn cmp_log(self, _: Self) -> Ordering {
        dead
    }

    #[logic(law)]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    #[trusted]
    fn cmp_le_log(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    #[trusted]
    fn cmp_lt_log(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    #[trusted]
    fn cmp_ge_log(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    #[trusted]
    fn cmp_gt_log(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    #[trusted]
    fn refl(x: Self) {}

    #[logic(law)]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    #[trusted]
    fn trans(x: Self, y: Self, z: Self, o: Ordering) {}

    #[logic(law)]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    #[trusted]
    fn antisym1(x: Self, y: Self) {}

    #[logic(law)]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    #[trusted]
    fn antisym2(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    #[trusted]
    fn eq_cmp(x: Self, y: Self) {}
}

pub type Timestamp = Int;

pub trait HasTimestamp {
    #[logic]
    fn get_timestamp(self, view: SyncView) -> Timestamp;

    #[logic(law)]
    #[ensures(x.le_log(y) == self.get_timestamp(x).le_log(self.get_timestamp(y)))]
    fn get_timestamp_monotonic(self, x: SyncView, y: SyncView);
}
