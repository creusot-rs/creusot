extern crate creusot_contracts;
use creusot_contracts::{logic::FMap, prelude::*};

#[ensures(result == m)]
pub fn complicated_identity<K, V>(m: Ghost<FMap<K, V>>) -> Ghost<FMap<K, V>> {
    ghost! {
        let mut result = FMap::new().into_inner();
        let len = snapshot!(m.len());

        let m_snap = snapshot!(m);

        #[variant(*len - produced.len())]
        #[invariant(forall<k, v> (m_snap.get(k) == Some(v)) == (result.get(k) == Some(v) || iter@.get(k) == Some(v)))]
        for (k, v) in m.into_inner() {
            result.insert_ghost(k, v);
        }

        proof_assert!(result.ext_eq(**m_snap));

        result
    }
}

#[ensures(*result == m1.merge(*m2, |(v1, _)| v1))]
pub fn merge_fmaps<K, V>(m1: Ghost<FMap<K, V>>, m2: Ghost<FMap<K, V>>) -> Ghost<FMap<K, V>> {
    ghost! {
        let merge = snapshot!(m1.merge(*m2, |(v1, _)| v1));
        let mut result = m2.into_inner();
        let len = snapshot!(m1.len());

        #[variant(*len - produced.len())]
        #[invariant(merge.ext_eq(iter@.merge(result, |(v1, _)| v1)))]
        for (k, v) in m1.into_inner() {
            result.insert_ghost(k, v);
        }

        proof_assert!(result.ext_eq(*merge));

        result
    }
}
