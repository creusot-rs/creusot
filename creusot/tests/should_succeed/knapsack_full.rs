extern crate creusot_contracts;
use creusot_contracts::{std::*, *};

struct Item<Name> {
    name: Name,
    weight: usize,
    value: usize,
}

#[logic]
fn max_log(a: Int, b: Int) -> Int {
    if a < b {
        b
    } else {
        a
    }
}

#[ensures(@result === max_log(@a, @b))]
fn max(a: usize, b: usize) -> usize {
    if a < b {
        b
    } else {
        a
    }
}

#[logic]
#[variant(s.len()-i)]
#[requires(0 <= i && i <= s.len())]
#[ensures(result >= 0)]
fn sum_weights<Name>(s: Seq<&Item<Name>>, i: Int) -> Int {
    pearlite! {
        if i == s.len() { 0 }
        else { @s[i].weight + sum_weights(s, i+1) }
    }
}

#[logic]
#[variant(s.len()-i)]
#[requires(i >= 0 && i <= s.len())]
fn sum_values<Name>(s: Seq<&Item<Name>>, i: Int) -> Int {
    pearlite! {
        if i == s.len() { 0 }
        else { @s[i].value + sum_values(s, i+1) }
    }
}

#[predicate]
#[variant(i2)]
#[requires(0 <= i1 && i1 <= s1.len())]
#[requires(0 <= i2 && i2 <= s2.len())]
fn subseq_rev<T>(s1: Seq<&T>, i1: Int, s2: Seq<T>, i2: Int) -> bool {
    pearlite! {
        if i2 == 0 { i1 == s1.len() }
        else {
          i1 < s1.len() && *s1[i1] === s2[i2 - 1] && subseq_rev(s1, i1+1, s2, i2-1) ||
          subseq_rev(s1, i1, s2, i2-1)
        }
    }
}

#[logic]
#[variant(i)]
#[requires(0 <= i && i <= items.len())]
#[requires(0 <= w)]
#[ensures(result >= 0)]
#[ensures(forall<s: Seq<&Item<Name>>, j: Int> 0 <= j && j <= s.len() && subseq_rev(s, j, items, i) && sum_weights(s, j) <= w ==>
    sum_values(s, j) <= result
)]
fn m<Name>(items: Seq<Item<Name>>, i: Int, w: Int) -> Int {
    pearlite! {
        if i == 0 { 0 }
        else if @items[i-1].weight > w {
            m(items, i-1, w)
        } else {
            max_log(m(items, i-1, w), m(items, i-1, w - @items[i-1].weight) + @items[i-1].value)
        }
    }
}

#[requires((@items).len() < 10000000)]
#[requires(@max_weight < 10000000)]
#[requires(forall<i: Int> 0 <= i && i < (@items).len() ==> @(@items)[i].value <= 10000000)]
#[ensures(sum_weights(@result, (@result).len()) <= @max_weight)]
#[ensures(subseq_rev(@result, 0, @items, (@items).len()))]
#[ensures(forall<s: Seq<&Item<Name>>> subseq_rev(s, 0, @items, (@items).len()) && sum_weights(s, s.len()) <= @max_weight ==>
    sum_values(s, s.len()) <= sum_values(@result, (@result).len())
)]
fn knapsack01_dyn<Name>(items: &Vec<Item<Name>>, max_weight: usize) -> Vec<&Item<Name>> {
    let mut best_value: Vec<Vec<usize>> =
        vec::from_elem(vec::from_elem(0, max_weight + 1), items.len() + 1);
    let mut i = 0;

    #[invariant(items_len, (@items).len() + 1 === (@best_value).len())]
    #[invariant(weight_len, forall<i: Int> 0 <= i && i < (@best_value).len() ==>
                  @max_weight + 1 === (@(@best_value)[i]).len())]
    #[invariant(best_value, forall<ii: Int, ww: Int> 0 <= ii && ii <= @i && 0 <= ww && ww <= @max_weight ==>
                  @(@(@best_value)[ii])[ww] === m(@items, ii, ww))]
    #[invariant(best_value_bounds, forall<ii: Int, ww: Int> 0 <= ii && ii <= (@items).len() && 0 <= ww && ww <= @max_weight ==>
                  @(@(@best_value)[ii])[ww] <= 10000000 * ii)]
    while i < items.len() {
        let it = &items[i];

        // Change compared to Rosetta Code: we start at w = 0.
        // This makes it possible to allow 0-weight items, and makes the proof simpler.
        let mut w = 0;

        #[invariant(items_len2, (@items).len() + 1 === (@best_value).len())]
        #[invariant(weight_len2, forall<i: Int> 0 <= i && i < (@best_value).len() ==>
                      @max_weight + 1 === (@(@best_value)[i]).len())]
        #[invariant(best_value2, forall<ii: Int, ww: Int>
                      0 <= ii && ii <= @i && 0 <= ww && ww <= @max_weight ==>
                      @(@(@best_value)[ii])[ww] === m(@items, ii, ww))]
        #[invariant(best_value2, forall<ww: Int> 0 <= ww && ww <= @w-1 ==>
                      @(@(@best_value)[@i+1])[ww] === m(@items, @i+1, ww))]
        #[invariant(best_value_bounds, forall<ii: Int, ww: Int> 0 <= ii && ii <= (@items).len() && 0 <= ww && ww <= @max_weight ==>
                  @(@(@best_value)[ii])[ww] <= 10000000 * ii)]
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

    let mut result: Vec<&_> = Vec::with_capacity(items.len());
    let mut left_weight = max_weight;

    let mut j = items.len();
    #[invariant(j_items_len, @j <= (@items).len())]
    #[invariant(left_weight_le_max, @left_weight <= @max_weight)]
    #[invariant(result_weight, forall<r: Seq<&Item<Name>>>
                (@result).len() <= r.len() &&
                (forall<i: Int> 0 <= i && i < (@result).len() ==> (@result)[i] === r[i]) &&
                sum_weights(r, (@result).len()) <= @left_weight ==>
                sum_weights(r, 0) <= @max_weight)]
    #[invariant(result_value, forall<r: Seq<&Item<Name>>>
                (@result).len() <= r.len() &&
                (forall<i: Int> 0 <= i && i < (@result).len() ==> (@result)[i] === r[i]) &&
                sum_values(r, (@result).len()) === m(@items, @j, @left_weight) ==>
                sum_values(r, 0) === m(@items, (@items).len(), @max_weight))]
    #[invariant(result_subseq, forall<r: Seq<&Item<Name>>>
                (@result).len() <= r.len() &&
                (forall<i: Int> 0 <= i && i < (@result).len() ==> (@result)[i] === r[i]) &&
                subseq_rev(r, (@result).len(), @items, @j) ==>
                subseq_rev(r, 0, @items, (@items).len()))]
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
