#![feature(allocator_api)]
#![allow(dead_code)]

extern crate creusot_contracts;
use creusot_contracts::{
    logic::{Int, Seq},
    *,
};

#[ensures((^str)@.len() >= len@ && (^str)@.len() >= str@.len())]
#[ensures((^str)@.len() == len@ || (^str)@.len() == str@.len())]
#[ensures(len@ <= str@.len() ==> (^str)@.len() == str@.len())]
#[ensures(len@ > str@.len() ==> (^str)@.len() == len@)]
#[ensures(forall<i: Int> 0 <= i && i < str@.len() ==> (^str)[i] == str[i])]
#[ensures(forall<i: Int> str@.len() <= i && i < len@ ==> (^str)[i] == pad)]
fn right_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T) {
    let old_str = snapshot! { str };

    #[invariant(^str == ^*old_str)]
    #[invariant(old_str@.len() <= str@.len())]
    #[invariant(old_str@.len() < len@ ==> str@.len() <= len@)]
    #[invariant(str@.len() > len@ ==> str@.len() == old_str@.len())]
    #[invariant(forall<i: Int> 0 <= i && i < old_str@.len() ==> str[i] == old_str[i])]
    #[invariant(forall<i: Int> old_str@.len() <= i && i < str@.len() ==> str[i] == pad)]
    while str.len() < len {
        str.push(pad);
    }
}

#[ensures((^str)@.len() >= len@ && (^str)@.len() >= str@.len())]
#[ensures((^str)@.len() == len@ || (^str)@.len() == str@.len())]
#[ensures(forall<i: Int> 0 <= i && i < ((^str)@.len() - str@.len()) ==> (^str)[i] == pad)]
#[ensures(forall<i: Int> 0 <= i && i < str@.len() ==> (^str)[i + ((^str)@.len() - str@.len())] == str[i])]
fn left_pad<T: Copy>(str: &mut Vec<T>, len: usize, pad: T) {
    let old_str = snapshot! { str };
    let mut c: Snapshot<Int> = snapshot! { 0 };

    #[invariant(^str == ^*old_str)]
    #[invariant(old_str@.len() <= str@.len())]
    #[invariant(old_str@.len() < len@ ==> str@.len() <= len@)]
    #[invariant(str@.len() > len@ ==> str@.len() == old_str@.len())]
    #[invariant(*c == str@.len() - old_str@.len())]
    #[invariant(forall<i: Int> *c <= i && i < str@.len() ==> str[i] == old_str[i - *c])]
    #[invariant(forall<i: Int> 0 <= i && i < *c ==> str[i] == pad)]
    while str.len() < len {
        str.insert(0, pad);
        c = snapshot! { 1 + *c };
    }
}

#[predicate]
fn is_unique<T>(s: Seq<T>) -> bool {
    pearlite! {
        forall<i: Int, j :Int> 0 <= i && i < s.len() && 0 <= j && j < s.len() ==> s[i] == s[j] ==> i == j
    }
}

#[predicate]
fn contains<T>(seq: Seq<T>, elem: T) -> bool {
    pearlite! {
        exists<i: Int> 0 <= i && i < seq.len() && seq[i] == elem
    }
}

#[predicate]
fn is_subset<T>(sub: Seq<T>, sup: Seq<T>) -> bool {
    pearlite! {
        forall<i: Int> 0 <= i && i < sub.len() ==> contains(sup, sub[i])
    }
}

#[logic]
#[ensures(is_subset(s, s.push(elem)))]
fn subset_push<T>(s: Seq<T>, elem: T) {}

#[requires(is_unique(vec.eq_model()))]
#[ensures(is_unique((^vec).eq_model()))]
#[ensures(is_subset(vec.eq_model(), (^vec).eq_model()))]
#[ensures(is_subset((^vec).eq_model(), vec.eq_model().push(elem.eq_model())))]
#[ensures(contains((^vec).eq_model(), elem.eq_model()))]
fn insert_unique<T: Eq + EqModel>(vec: &mut Vec<T>, elem: T) {
    snapshot! { subset_push::<T::EqModelTy> };
    proof_assert! { is_subset(vec.eq_model(), vec.eq_model().push(elem.eq_model())) };
    let ghost_vec = snapshot! { vec };

    #[invariant(forall<j: Int> 0 <= j && j < produced.len() ==> produced[j].eq_model() != elem.eq_model())]
    for e in vec.iter() {
        proof_assert! { *e == ghost_vec[produced.len()-1] };
        if e == &elem {
            proof_assert! { contains(vec.eq_model(), elem.eq_model()) };
            return;
        }
    }

    proof_assert!(^vec == ^*ghost_vec);
    proof_assert! { is_unique(vec.eq_model().push(elem.eq_model())) };
    vec.push(elem);
}

#[ensures(is_unique(result.eq_model()))]
#[ensures(is_subset(result.eq_model(), str.eq_model()))]
#[ensures(is_subset(str.eq_model(), result.eq_model()))]
fn unique<T: Eq + EqModel + Copy>(str: &[T]) -> Vec<T> {
    let mut unique = Vec::new();
    let mut sub_str: Snapshot<Seq<T>> = snapshot! { Seq::EMPTY };

    #[invariant(is_unique(unique.eq_model()))]
    #[invariant(is_subset(unique.eq_model(), str.eq_model()))]
    #[invariant(is_subset(str.eq_model().subsequence(0, produced.len()), unique.eq_model()))]
    for i in 0..str.len() {
        let elem: T = str[i];
        insert_unique(&mut unique, elem);
        sub_str = snapshot! { sub_str.push(elem) };
    }

    proof_assert! { is_subset(str.eq_model().subsequence(0, str@.len()), unique.eq_model()) }
    proof_assert! { str.eq_model().subsequence(0, str@.len()).ext_eq(str.eq_model()) }
    unique
}

#[logic]
#[variant(to - from)]
#[requires(0 <= from && from <= to && to <= seq.len())]
#[ensures(result >= 0)]
fn sum_range(seq: Seq<u32>, from: Int, to: Int) -> Int {
    if to - from > 0 {
        pearlite! { seq[from]@ + sum_range(seq, from + 1, to) }
    } else {
        0
    }
}

#[logic]
#[variant(i - from)]
#[requires(0 <= from && from <= i && i <= to && to <= seq.len())]
#[ensures(sum_range(seq, from, to) == sum_range(seq, from, i) + sum_range(seq, i, to))]
fn sum_range_split(seq: Seq<u32>, from: Int, to: Int, i: Int) {
    if i > from {
        sum_range_split(seq, from + 1, to, i);
    }
}

#[logic]
#[requires(0 <= i && i <= seq.len())]
#[ensures(0 <= result && result <= sum_range(seq, 0 , seq.len()))]
#[ensures(0 == i || i == seq.len() ==> result == sum_range(seq, 0, seq.len()))]
fn score(seq: Seq<u32>, i: Int) -> Int {
    sum_range_split(seq, 0, seq.len(), i);
    sum_range(seq, 0, i).abs_diff(sum_range(seq, i, seq.len()))
}

// Fulcrum. Given a sequence of integers, returns the index i that minimizes
// |sum(seq[..i]) - sum(seq[i..])|. Does this in O(n) time and O(n) memory.
// Hard
#[requires(sum_range(s@, 0, s@.len()) <= 1000)]
#[requires(s@.len() > 0)]
#[ensures(0 <= result@ && result@ < s@.len())]
#[ensures(forall<i: Int> 0 <= i && i < s@.len() ==> score(s@, result@) <= score(s@, i))]
fn fulcrum(s: &[u32]) -> usize {
    let mut total: u32 = 0;

    #[invariant(total@ == sum_range(s@, 0, produced.len()))]
    #[invariant(total@ <= sum_range(s@, 0, s@.len()))]
    for &x in s {
        total += x;
    }

    proof_assert! { total@ == sum_range(s@, 0, s@.len()) };

    let mut min_i: usize = 0;
    let mut min_dist: u32 = total;

    let mut sum: u32 = 0;
    #[invariant(sum@ == sum_range(s@, 0, produced.len()))]
    #[invariant(sum@ <= total@)]
    #[invariant(min_i@ <= produced.len() && min_i@ < s@.len())]
    #[invariant(min_dist@ == score(s@, min_i@))]
    #[invariant(forall<j: Int> 0 <= j && j < produced.len() ==> score(s@, min_i@) <= score(s@, j))]
    for i in 0..s.len() {
        let dist = sum.abs_diff(total - sum);
        if dist < min_dist {
            min_i = i;
            min_dist = dist;
        }

        sum += s[i];
    }

    min_i
}
