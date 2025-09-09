extern crate creusot_contracts;
use creusot_contracts::{vec, *};

pub struct Item<Name> {
    pub name: Name,
    pub weight: usize,
    pub value: usize,
}

#[requires(true)]
#[ensures(result@ == a@.max(b@))]
fn max(a: usize, b: usize) -> usize {
    if a < b { b } else { a }
}

/// Check that values stored in ``best_value`` correspond to the function ``m`` from
/// https://en.wikipedia.org/wiki/Knapsack_problem#0/1_knapsack_problem
///
/// *   $m[0,\,w]=0$
/// *   $m[i,\,w]=m[i-1,\,w]$ if $w_i > w\,\!$ (the new item is more than the current weight limit)
/// *   $m[i,\,w]=\max(m[i-1,\,w],\,m[i-1,w-w_i]+v_i)$ if $w_i \leqslant w$.
#[logic]
#[variant(i)]
#[requires(0 <= i && i <= items.len())]
#[requires(0 <= w)]
#[ensures(result >= 0)]
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
pub fn knapsack01_dyn<Name>(items: &Vec<Item<Name>>, max_weight: usize) -> Vec<&Item<Name>> {
    let mut best_value = vec![vec![0; max_weight + 1]; items.len() + 1];
    let mut i = 0;

    #[invariant(items@.len() + 1 == best_value@.len())]
    #[invariant(forall<i> 0 <= i && i < best_value@.len() ==>
                max_weight@ + 1 == (best_value[i]@).len())]
    #[invariant(forall<ii, ww> 0 <= ii && ii <= i@ && 0 <= ww && ww <= max_weight@ ==>
                  (best_value[ii]@)[ww]@ == m(items@, ii, ww))]
    #[invariant(forall<ii, ww> 0 <= ii && ii <= items@.len() && 0 <= ww && ww <= max_weight@ ==>
                  (best_value[ii]@)[ww]@ <= 10000000 * ii)]
    while i < items.len() {
        let it = &items[i];

        // Change compared to Rosetta Code: we start at w = 0.
        // This makes it possible to allow 0-weight items, and makes the proof simpler.
        let mut w = 0;

        #[invariant(items@.len() + 1 == best_value@.len())]
        #[invariant(forall<i> 0 <= i && i < best_value@.len() ==>
                      max_weight@ + 1 == (best_value[i]@).len())]
        #[invariant(forall<ii, ww>
                      0 <= ii && ii <= i@ && 0 <= ww && ww <= max_weight@ ==>
                      (best_value[ii]@)[ww]@ == m(items@, ii, ww))]
        #[invariant(forall<ww> 0 <= ww && ww <= w@-1 ==>
                      (best_value[i@+1]@)[ww]@ == m(items@, i@+1, ww))]
        #[invariant(forall<ii, ww> 0 <= ii && ii <= items@.len() && 0 <= ww && ww <= max_weight@ ==>
                  (best_value[ii]@)[ww]@ <= 10000000 * ii)]
        while w <= max_weight {
            best_value[i + 1][w] = if it.weight > w {
                best_value[i][w]
            } else {
                max(best_value[i][w], best_value[i][w - it.weight] + it.value)
            };
            w += 1
        }
        i += 1
    }

    let mut result = Vec::with_capacity(items.len());
    let mut left_weight = max_weight;

    let mut j = items.len();
    #[invariant(inv(result))]
    #[invariant(j@ <= items@.len())]
    #[invariant(left_weight@ <= max_weight@)]
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
