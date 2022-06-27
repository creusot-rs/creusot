extern crate creusot_contracts;
use creusot_contracts::*;

#[predicate]
fn sorted_range(s: Seq<u32>, l: Int, u: Int) -> bool {
    pearlite! {
        forall<i: Int, j :Int> l <= i && i < j && j < u ==> s[i] <= s[j]
    }
}

#[ensures(sorted_range((@^v), 0, (@^v).len()))]
#[ensures((@^v).permutation_of(@v))]
pub fn sort(v: &mut Vec<u32>) {
    let mut i: usize = 1;
    let old_v = ghost! { v };

    if v.len() == 0 {
        return;
    }

    #[invariant(proph_const, ^v == ^*old_v)]
    #[invariant(permutation, (@old_v).permutation_of(@v))]
    #[invariant(sorted, sorted_range((@v), 0, @i))]
    #[invariant(i_bound, @i <= (@v).len())]
    while i < v.len() {
        let x = v[i];

        let mut j = i;
        proof_assert! { (@v).set(@j, x).ext_eq(@v) };
        #[invariant(j_bound, 0 <= @j && @j <= @i)]
        #[invariant(proph_const, ^v == ^*old_v)]
        #[invariant(a, forall<k1 : _, k2: _> 0 <= k1 && k1 <= k2 && k2 <= @i ==> k1 != @j ==> k2 != @j ==> (@v)[k1] <= (@v)[k2] )]
        #[invariant(perm, (@old_v).permutation_of((@v).set(@j, x)))]
        #[invariant(_xx, forall<k : _> @j + 1 <= k && k <= @i ==> x < (@v)[k])]
        #[invariant(_len, (@old_v).len() == (@v).len())]
        while j > 0 && v[j-1] > x {
            let v_at_L = ghost! { v.model() };
            v[j] = v[j-1];
            proof_assert!{ v_at_L.set(@j, x).exchange((@v).set(@j - 1, x), @j - 1, @j)}
            j -= 1;
        }
        let hack = ghost! { v.model() };
        v[j] = x;
        // The spec for `index_mut` is probably not the best... so let's just assert exactly what we want here. 
        proof_assert! { (@v).ext_eq(hack.set(@j, x)) };
        proof_assert! { forall<k : _> 0 <= k && k < @j ==> (@v)[k] <= x };
        i += 1;
    }
}
