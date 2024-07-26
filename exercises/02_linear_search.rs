extern crate creusot_contracts;
use creusot_contracts::*;

// Prove the following:
// 1. If we return Some(i) it is the first index containing `tgt`
// 2. If we return None, then there are no indices containing `tgt`
fn search<T: Ord + DeepModel>(v: &[T], tgt: &T) -> Option<usize> {
    let mut i = 0;

    while i < v.len() {
        if v[i] == *tgt {
            return Some(i);
        }

        i += 1
    }

    return None;
}
