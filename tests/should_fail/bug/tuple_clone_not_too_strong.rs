// WHY3PROVE
// Counter-example: the synthesized tuple-`Clone` law is per-field-to-source, NOT
// cross-field. A false cross-field property must therefore be UNprovable — this
// pins that the law is not accidentally too strong (a soundness boundary).
extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result.0 == result.1)] // must NOT hold for e.g. (3, 7)
pub fn clone_not_cross_field(x: (u32, u32)) -> (u32, u32) {
    x.clone()
}
