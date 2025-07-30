extern crate creusot_contracts;
use creusot_contracts::{
    invariant::inv,
    logic::{Int, Seq},
    vec, *,
};

pub struct Item<Name> {
    pub name: Name,
    pub weight: usize,
    pub value: usize,
}

#[ensures(result@ == a@.max(b@))]
fn max(a: usize, b: usize) -> usize {
    if a < b { b } else { a }
}

#[logic]
#[variant(s.len()-i)]
#[requires(0 <= i && i <= s.len())]
#[ensures(result >= 0)]
fn sum_weights<Name>(s: Seq<&Item<Name>>, i: Int) -> Int {
    pearlite! {
        if i == s.len() { 0 }
        else { s[i].weight@ + sum_weights(s, i+1) }
    }
}

#[logic]
#[variant(s.len()-i)]
#[requires(i >= 0 && i <= s.len())]
fn sum_values<Name>(s: Seq<&Item<Name>>, i: Int) -> Int {
    pearlite! {
        if i == s.len() { 0 }
        else { s[i].value@ + sum_values(s, i+1) }
    }
}

#[logic]
#[variant(i2)]
#[requires(0 <= i1 && i1 <= s1.len())]
#[requires(0 <= i2 && i2 <= s2.len())]
fn subseq_rev<T>(s1: Seq<&T>, i1: Int, s2: Seq<T>, i2: Int) -> bool {
    pearlite! {
        if i2 == 0 { i1 == s1.len() }
        else {
          i1 < s1.len() && *s1[i1] == s2[i2 - 1] && subseq_rev(s1, i1+1, s2, i2-1) ||
          subseq_rev(s1, i1, s2, i2-1)
        }
    }
}

#[logic]
#[variant(i)]
#[requires(0 <= i && i <= items.len())]
#[requires(0 <= w)]
#[ensures(result >= 0)]
#[ensures(forall<s: Seq<&Item<Name>>, j> 0 <= j && j <= s.len() && subseq_rev(s, j, items, i) && sum_weights(s, j) <= w ==>
    sum_values(s, j) <= result
)]
fn m<Name>(items: Seq<Item<Name>>, i: Int, w: Int) -> Int {
    pearlite! {
        if i == 0 { 0 }
        else if items[i-1].weight@ > w {
            m(items, i-1, w)
        } else {
            m(items, i-1, w).max(m(items, i-1, w - items[i-1].weight@) + items[i-1].value@)
        }
    }
}

#[requires(items@.len() < 10000000)]
#[requires(max_weight@ < 10000000)]
#[requires(forall<i> 0 <= i && i < items@.len() ==> items[i].value@ <= 10000000)]
#[ensures(sum_weights(result@, result@.len()) <= max_weight@)]
#[ensures(subseq_rev(result@, 0, items@, items@.len()))]
#[ensures(forall<s: Seq<&Item<Name>>> subseq_rev(s, 0, items@, items@.len()) && sum_weights(s, s.len()) <= max_weight@ ==>
    sum_values(s, s.len()) <= sum_values(result@, result@.len())
)]
pub fn knapsack01_dyn<Name>(items: &Vec<Item<Name>>, max_weight: usize) -> Vec<&Item<Name>> {
    let mut best_value = vec![vec![0; max_weight + 1]; items.len() + 1];

    #[invariant(items@.len() + 1 == best_value@.len())]
    #[invariant(forall<i> 0 <= i && i < best_value@.len() ==>
                  max_weight@ + 1 == (best_value[i]@).len())]
    #[invariant(forall<ii, ww> 0 <= ii && ii <= produced.len() && 0 <= ww && ww <= max_weight@ ==>
                  (best_value[ii]@)[ww]@ == m(items@, ii, ww))]
    #[invariant(forall<ii, ww> 0 <= ii && ii <= items@.len() && 0 <= ww && ww <= max_weight@ ==>
                  (best_value[ii]@)[ww]@ <= 10000000 * ii)]
    for i in 0..items.len() {
        let it = &items[i];

        #[invariant(items@.len() + 1 == best_value@.len())]
        #[invariant(forall<i> 0 <= i && i < best_value@.len() ==>
                      max_weight@ + 1 == (best_value[i]@).len())]
        #[invariant(forall<ii, ww>
                      0 <= ii && ii <= i@ && 0 <= ww && ww <= max_weight@ ==>
                      (best_value[ii]@)[ww]@ == m(items@, ii, ww))]
        #[invariant(forall<ww> 0 <= ww && ww <= produced.len() - 1 ==>
                      (best_value[i@+1]@)[ww]@ == m(items@, i@+1, ww))]
        #[invariant(forall<ii, ww> 0 <= ii && ii <= items@.len() && 0 <= ww && ww <= max_weight@ ==>
                  (best_value[ii]@)[ww]@ <= 10000000 * ii)]
        // Change compared to Rosetta Code: we start at w = 0.
        // This makes it possible to allow 0-weight items, and makes the proof simpler.
        for w in 0..=max_weight {
            best_value[i + 1][w] = if it.weight > w {
                best_value[i][w]
            } else {
                max(best_value[i][w], best_value[i][w - it.weight] + it.value)
            };
        }
    }

    let mut result: Vec<&_> = Vec::with_capacity(items.len());
    let mut left_weight = max_weight;

    let mut j = items.len();
    #[invariant(inv(result))]
    #[invariant(j@ <= items@.len())]
    #[invariant(left_weight@ <= max_weight@)]
    #[invariant(forall<r: Seq<&Item<Name>>>
                    result@.len() <= r.len() &&
                    (forall<i> 0 <= i && i < result@.len() ==> result[i] == r[i]) &&
                    sum_values(r, result@.len()) == m(items@, j@, left_weight@) ==>
                    sum_values(r, 0) == m(items@, items@.len(), max_weight@))]
    #[invariant(forall<r: Seq<&Item<Name>>>
                    result@.len() <= r.len() &&
                    (forall<i> 0 <= i && i < result@.len() ==> result[i] == r[i]) &&
                    sum_weights(r, result@.len()) <= left_weight@ ==>
                    sum_weights(r, 0) <= max_weight@)]
    #[invariant(forall<r: Seq<&Item<Name>>>
                    result@.len() <= r.len() &&
                    (forall<i> 0 <= i && i < result@.len() ==> result[i] == r[i]) &&
                    subseq_rev(r, result@.len(), items@, j@) ==>
                    subseq_rev(r, 0, items@, items@.len()))]
    while 0 < j {
        j -= 1;
        let it = &items[j];
        if best_value[j + 1][left_weight] != best_value[j][left_weight] {
            result.push(it);
            left_weight -= it.weight;
        }
    }

    result
}
