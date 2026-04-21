use creusot_std::prelude::*;

#[bitwise_proof]
#[ensures(result == forall<i> 0 <= i && i < values@.len() ==> values@[i].leading_zeros_logic() < max)]
pub fn all_ldz(values: [u64; 25], max: u32) -> bool {
    let mut i = 0;

    #[invariant(forall<j> 0 <= j  && j < i@ ==> values@[j].leading_zeros_logic() < max)]
    while i < values.len() {
        if values[i].leading_zeros() >= max {
            return false;
        }

        i += 1;
    }

    true
}

#[bitwise_proof]
#[requires(boolvec@.len() < 64)]
#[ensures(forall<i: u64> 0 <= i@ && i@ < boolvec@.len() ==> (^bitvec) & 1u64 << i != 0u64 == boolvec@[i@])]
pub fn boolvec_to_bitvec(boolvec: &[bool], bitvec: &mut u64) {
    let mut i = 0;

    #[invariant(forall<j: u64> 0 <= j@ && j@ < i@ ==> ((*bitvec) & 1u64 << j != 0u64) == boolvec@[j@])]
    while i < boolvec.len() {
        if boolvec[i] {
            *bitvec |= 1 << i;
        } else {
            *bitvec &= !(1 << i);
        }

        i += 1;
    }
}
