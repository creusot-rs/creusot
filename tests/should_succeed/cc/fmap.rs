extern crate creusot_std;
use creusot_std::{
    logic::{FMap, LexFMap},
    prelude::*,
};

#[ensures(*result == 2usize)]
pub fn resolves() -> Ghost<usize> {
    ghost! {
        let mut k = 0;
        let mut v = 0;
        let mut s = FMap::new().into_inner();
        let bor_k = &mut k;
        let bor_v = &mut v;
        let snap_k = snapshot!{ bor_k };
        let snap_v = snapshot!{ bor_v };
        s.insert(bor_k, bor_v);
        #[invariant(produced.len() <= 1)]
        #[invariant(produced.len() == 0 || ^snap_k == 1usize && ^snap_v == 1usize)]
        #[variant(1 - produced.len())]
        for (k2, v2) in s {
            *k2 = 1;
            *v2 = 1;
        }
        k + v
    }
}

#[requires(k < l)]
#[requires(v < w)]
pub fn ord<K: Copy + OrdLogic, V: Copy + OrdLogic>(k: K, l: K, v: V, w: V) {
    ghost! {
        let mut kv = FMap::new().into_inner();
        kv.insert(k, v);
        proof_assert! { LexFMap(FMap::empty()) < LexFMap(kv) };

        let mut kw = FMap::new().into_inner();
        kw.insert(k, w);
        proof_assert! { LexFMap(kv) < LexFMap(kw) };

        let mut lv = FMap::new().into_inner();
        lv.insert(l, v);
        proof_assert! { LexFMap(kv) < LexFMap(lv) };
    };
}
