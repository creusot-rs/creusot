extern crate creusot_std;
use ::std::ops::Bound;

// This generates "fake refs" for borrow checking that should be ignored otherwise
pub fn range(range: Bound<&usize>) -> usize {
    match range {
        Bound::Included(&end) if end == 0 => 0,
        Bound::Excluded(&end) if end == 0 => 0,
        _ => 1,
    }
}
