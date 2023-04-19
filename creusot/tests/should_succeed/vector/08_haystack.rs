// This example was tken from an issue of @yannickmoy (#309).
// It performs a 'substring' match between two vectors of u8.
extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

#[predicate]
fn match_at(needle: &Vec<u8>, haystack: &Vec<u8>, pos: Int, len: Int) -> bool {
    pearlite! { len <= needle@.len()
      && pos <= haystack@.len() - len
      && forall<i: Int>
          0 <= i && i < len ==> needle@[i] == haystack@[pos + i]
    }
}

#[requires(needle@.len() >= 1 && needle@.len() <= haystack@.len())]
#[ensures(@result == haystack@.len() || @result < haystack@.len() - needle@.len() + 1)]
#[ensures(@result < haystack@.len() ==>
            match_at(needle, haystack, @result, needle@.len())
             && (forall <i: Int> 0 <= i && i < @result ==> ! match_at(needle, haystack, i, needle@.len())))]
#[ensures(@result == haystack@.len() ==> forall <i: Int> 0 <= i && i < haystack@.len() ==> ! match_at(needle, haystack, i, needle@.len()))]
pub fn search(needle: &Vec<u8>, haystack: &Vec<u8>) -> usize {
    #[invariant(no_match,forall<k: Int> 0 <= k && k < produced.len() ==> ! match_at(needle, haystack, k, needle@.len()))]
    'a: for i in 0..=haystack.len() - needle.len() {
        #[invariant(partial_match,match_at(needle, haystack, @i, produced.len()))]
        for j in 0..needle.len() {
            if needle[j] != haystack[i + j] {
                continue 'a;
            }
        }

        return i;
    }
    return haystack.len();
}
