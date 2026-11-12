extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x.deep_model() == y.deep_model())]
#[ensures(result == (x, x, y, y))]
pub fn min_on_tie<T: Copy + Ord + DeepModel<DeepModelTy: OrdLogic>>(x: T, y: T) -> (T, T, T, T) {
    (x.min(y), std::cmp::min(x, y), x.max(y), std::cmp::max(x, y))
}
