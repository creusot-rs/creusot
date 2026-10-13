extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn is_sorted_logic(elems: Seq<i32>, start: Int, end: Int) -> bool {
    pearlite! {
        forall<i, j> start <= i && i < j && j < end ==> elems[i]@ <= elems[j]@
    }
}

#[logic_alias(is_sorted_logic(data@, 0, data@.len()))]
pub fn is_sorted(data: Vec<i32>) -> bool {
    if data.len() < 2 {
        return true;
    }

    let mut i = 1;

    #[invariant(is_sorted_logic(data@, 0, i@) && i@ > 0)]
    while i < data.len() {
        if data[i] < data[i - 1] {
            return false;
        }

        i += 1;
    }

    true
}

#[ensures(is_sorted(^v))]
#[ensures((^v)@.permutation_of(v@))]
pub fn gnome_sort(v: &mut Vec<i32>) {
    let old_v = snapshot! { v };
    let mut i = 0;
    #[invariant(is_sorted_logic(v@, 0, i@))]
    #[invariant(v@.permutation_of(old_v@))]
    while i < v.len() {
        if i == 0 || v[i - 1] <= v[i] {
            i += 1;
        } else {
            v.swap(i - 1, i);
            i -= 1;
        }
    }
}
