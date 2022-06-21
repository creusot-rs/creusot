// This example was tken from an issue of @yannickmoy (#309).
// It performs a 'substring' match between two vectors of u8.
extern crate creusot_contracts;
use creusot_contracts::*;

#[predicate]
fn match_at(needle: &Vec<u8>, haystack: &Vec<u8>, pos: Int, len: Int) -> bool {
    pearlite! { len <= (@needle).len()
      && pos <= (@haystack).len() - len
      && forall<i: Int>
          0 <= i && i < len ==> (@needle)[i] == (@haystack)[pos + i]
    }
}

#[requires((@needle).len() >= 1 && (@needle).len() <= (@haystack).len())]
#[ensures(@result == (@haystack).len() || @result < (@haystack).len() - (@needle).len() + 1)]
#[ensures(@result < (@haystack).len() ==>
            match_at(needle, haystack, @result, (@needle).len())
             && (forall <i: Int> 0 <= i && i < @result ==> ! match_at(needle, haystack, i, (@needle).len())))]
#[ensures(@result == (@haystack).len() ==> forall <i: Int> 0 <= i && i < (@haystack).len() ==> ! match_at(needle, haystack, i, (@needle).len()))]
pub fn search(needle: &Vec<u8>, haystack: &Vec<u8>) -> usize {
    let mut i: usize = 0;
    #[invariant(no_match,forall<k: Int> 0 <= k && k < @i ==> ! match_at(needle, haystack, k, (@needle).len()))]
    while i < haystack.len() - needle.len() + 1 {
        let mut j: usize = 0;
        #[invariant(partial_match,match_at(needle, haystack, @i, @j))]
        while j < needle.len() {
            proof_assert!(@j <= (@needle).len());
            if needle[j] != haystack[i + j] {
                break;
            }
            j += 1;
        }

        if j == needle.len() {
            return i;
        };

        i += 1
    }
    return haystack.len();
}
