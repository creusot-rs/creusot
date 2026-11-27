//! This module defines:
//! - [`card`], a counting primitive for a predicate over the integers,
//! - the [`Seq::injective_into`] and [`Seq::surjective_onto`]
//!     predicates for [`Seq<Int>`], and how they relate to each
//!     other and to [`Seq::len()`],
//! - [`Seq::count`], a logic function counting the number of occurences
//!     of an object in a [`Seq<T>`],
//! - [`Seq::permutation_of`], a predicate for whether two sequences
//!     are permutations of one another, and theorems to use it.

use crate::{logic, logic::Mapping, prelude::*};

/*
    card and theorems
*/

/// Counts the number of integers `i` in the range `a..b` such
/// that `p[i]`.
/// Returns `0` when the range is empty (when `a >= b`).
///
/// # Example
/// ```rust,creusot
/// use creusot_std::logic::card;
/// proof_assert!(card(-2, 6, |i| i % 2 == 0) == 4);
/// ```
#[logic(open)]
#[requires(a <= b)]
#[ensures(0 <= result && result <= b - a)]
#[variant(b - a)]
pub fn card(a: Int, b: Int, p: Mapping<Int, bool>) -> Int {
    if a >= b { 0 } else { card(a, b - 1, p) + if p[b - 1] { 1 } else { 0 } }
}

/// Congruence lemma for `card`. If two predicates are equivalent
/// on the range that is considered, the cardinals are equal.
#[logic(opaque)]
#[requires(a <= b)]
#[requires(forall<i> a <= i && i < b ==> p1[i] == p2[i])]
#[ensures(card(a, b, p1) == card(a, b, p2))]
#[variant(b - a)]
pub fn card_congr(a: Int, b: Int, p1: Mapping<Int, bool>, p2: Mapping<Int, bool>) {
    if a < b {
        card_congr(a, b - 1, p1, p2);
    }
}

/// The cardinal is zero if an only if the predicate is false on the whole range.
/// The conclusion may also be useful in the following form:
/// `(card(a, b, p) > 0) == (exists<i> a <= i && i < b && p[i])`.
#[logic(opaque)]
#[requires(a <= b)]
#[ensures((card(a, b, p) == 0) == (forall<i> a <= i && i < b ==> !p[i]))]
#[variant(b - a)]
pub fn card_false(a: Int, b: Int, p: Mapping<Int, bool>) {
    if a < b {
        card_false(a, b - 1, p);
    }
}

/// The cardinal is `b - a` if and only if the predicate is true on the whole range.
/// The conclusion may also be useful in the following form:
/// `(card(a, b, p) < b - a) == (exists<i> a <= i && i < b && !p[i])`.
#[logic(opaque)]
#[requires(a <= b)]
#[ensures((card(a, b, p) == b - a) == (forall<i> a <= i && i < b ==> p[i]))]
#[variant(b - a)]
pub fn card_true(a: Int, b: Int, p: Mapping<Int, bool>) {
    if a < b {
        card_true(a, b - 1, p);
    }
}

/// The cardinal is at least `2` if and only if the predicate is true for two distinct integers.
/// The conclusion may also be useful in the following form:
/// `(card(a, b, p) <= 1) == (forall<i, j> a <= i && i <= j && j < b ==> p[i] && p[j] ==> i == j)`.
#[logic(opaque)]
#[requires(a <= b)]
#[ensures((card(a, b, p) >= 2) == (exists<i, j> a <= i && i < j && j < b && p[i] && p[j]))]
#[variant(b - a)]
pub fn card_ge_2(a: Int, b: Int, p: Mapping<Int, bool>) {
    if a < b {
        if p[b - 1] {
            card_false(a, b - 1, p);
        } else {
            card_ge_2(a, b - 1, p);
        }
    }
}

/// The cardinal of two disjoint subsets is equal to the sum of the two cardinals.
#[logic(opaque)]
#[requires(a <= b)]
#[requires(forall<i> a <= i && i < b ==> !(p1[i] && p2[i]))]
#[requires(forall<i> a <= i && i < b ==> p[i] == (p1[i] || p2[i]))]
#[ensures(card(a, b, p) == card(a, b, p1) + card(a, b, p2))]
#[variant(b - a)]
pub fn card_disjoint(
    a: Int,
    b: Int,
    p1: Mapping<Int, bool>,
    p2: Mapping<Int, bool>,
    p: Mapping<Int, bool>,
) {
    if a < b {
        card_disjoint(a, b - 1, p1, p2, p);
    }
}

/// Chasles's relation for `card`.
#[logic(opaque)]
#[requires(a <= b && b <= c)]
#[ensures(card(a, c, p) == card(a, b, p) + card(b, c, p))]
#[variant(c - b)]
pub fn card_join(a: Int, b: Int, c: Int, p: Mapping<Int, bool>) {
    if b < c {
        card_join(a, b, c - 1, p);
    }
}

/*
    injectivity, surjectivity and theorems
*/

impl Seq<Int> {
    /// This predicate is true if and only if `self` is injective
    /// and contains only elements in the integral range `0..n`.
    #[logic(open)]
    pub fn injective_into(self, n: Int) -> bool {
        pearlite! {
            (forall<i> 0 <= i && i < self.len() ==> 0 <= self[i] && self[i] < n) &&
            forall<i1, i2> 0 <= i1 && i1 <= i2 && i2 < self.len() ==> self[i1] == self[i2] ==> i1 == i2
        }
    }

    /// This predicate is true if and only if `self` contains every
    /// integer in the range `0..n`.
    #[logic(open)]
    pub fn surjective_onto(self, n: Int) -> bool {
        pearlite! {
            forall<j> 0 <= j && j < n ==> self.contains(j)
        }
    }

    /// A sequence that is surjective onto `0..n` has length at least `n`.
    #[logic(opaque)]
    #[requires(self.surjective_onto(n))]
    #[ensures(self.len() >= n)]
    pub fn length_surj(self, n: Int) {
        if 0 <= n {
            surj_aux(self, 0, n);
        }
    }

    /// A sequence that is injective into `0..n` has length at most `n`.
    #[logic(opaque)]
    #[requires(self.injective_into(n))]
    #[requires(0 <= n)]
    #[ensures(self.len() <= n)]
    pub fn length_inj(self, n: Int) {
        inj_aux(self, n, self.len());
    }

    /// A permutation of `0..n` has length exactly `n`.
    #[logic(opaque)]
    #[requires(self.injective_into(n) && self.surjective_onto(n))]
    #[requires(0 <= n)]
    #[ensures(self.len() == n)]
    pub fn length_bij(self, n: Int) {
        self.length_surj(n);
        self.length_inj(n);
    }

    /// An surjection onto `0..n` of length at most `n` is a permutation of `0..n`.
    #[logic(opaque)]
    #[requires(self.surjective_onto(n))]
    #[requires(self.len() <= n)]
    #[ensures(self.injective_into(n))]
    #[ensures(self.len() == n)]
    pub fn inj_of_surj(self, n: Int) {
        pearlite! {
            surj_aux(self, 0, n);
            card_true(0, n, |i| 0 <= self[i] && self[i] < n);
            proof_assert!(forall<i> 0 <= i && i < self.len() ==> 0 <= self[i] && self[i] < n);

            if (exists<i1, i2> 0 <= i1 && i1 <= i2 && i2 < self.len() && self[i1] == self[i2] && i1 != i2) {
                let (i1, i2) = logic::such_that(|(i1, i2)|
                    0 <= i1 && i1 <= i2 && i2 < self.len() && self[i1] == self[i2] && i1 != i2
                );
                surj_aux_ne(self, n, self[i1]);
                proof_assert!(card(0, self.len(), |i| self[i] != self[i1]) >= n - 1);
                card_ge_2(0, self.len(), |i| self[i] == self[i1]);
                proof_assert!(card(0, self.len(), |i| self[i] == self[i1]) >= 2);
                card_disjoint(0, self.len(), |i| self[i] != self[i1], |i| self[i] == self[i1], |_| true);
                card_true(0, self.len(), |_| true);
                proof_assert!(self.len() >= n + 1);
            } else {
                self.length_inj(n);
            }
        }
    }

    /// An injection into `0..n` of length at least `n` is a permutation of `0..n`.
    #[logic(opaque)]
    #[requires(self.injective_into(n))]
    #[requires(self.len() >= n)]
    #[requires(0 <= n)]
    #[ensures(self.surjective_onto(n))]
    #[ensures(self.len() == n)]
    pub fn surj_of_inj(self, n: Int) {
        pearlite! {
            inj_aux(self, n, self.len());
            proof_assert!(n == self.len());
            let f = |j| self.contains(j);
            proof_assert!(card(0, n, f) == n);
            card_true(0, n, f);
            inj_helper(self, n);
        }
    }
}

//private lemmas
#[logic(opaque)]
#[requires(a <= j)]
#[requires(forall<k> a <= k && k < j ==> s.contains(k))]
#[ensures(card(0, s.len(), |i| a <= s[i] && s[i] < j) >= j - a)]
#[variant(j - a)]
fn surj_aux(s: Seq<Int>, a: Int, j: Int) {
    if a < j {
        surj_aux(s, a, j - 1);
        proof_assert!(exists<i> 0 <= i && i < s.len() && s[i] == j - 1);
        card_false(0, s.len(), |i| s[i] == j - 1);
        proof_assert!(card(0, s.len(), |i| s[i] == j - 1) >= 1);
        card_disjoint(
            0,
            s.len(),
            |i| s[i] == j - 1,
            |i| a <= s[i] && s[i] < j - 1,
            |i| a <= s[i] && s[i] < j,
        );
        proof_assert!(
            card(0, s.len(), |i| a <= s[i] && s[i] < j)
                == card(0, s.len(), |i| a <= s[i] && s[i] < j - 1)
                    + card(0, s.len(), |i| s[i] == j - 1)
        );
    }
}

#[logic(opaque)]
#[requires(forall<i> 0 <= i && i < s.len() ==> 0 <= s[i] && s[i] < n)]
#[requires(forall<j> 0 <= j && j < n ==> s.contains(j))]
#[requires(0 <= k && k < n)]
#[ensures(card(0, s.len(), |i| s[i] != k) >= n - 1)]
fn surj_aux_ne(s: Seq<Int>, n: Int, k: Int) {
    surj_aux(s, 0, k);
    surj_aux(s, k + 1, n);
    card_disjoint(
        0,
        s.len(),
        |i| 0 <= s[i] && s[i] < k,
        |i| k + 1 <= s[i] && s[i] < n,
        |i| s[i] != k,
    );
}

#[logic(opaque)]
#[requires(0 <= n)]
#[requires(forall<i1, i2> 0 <= i1 && i1 <= i2 && i2 < s.len() ==> s[i1] == s[i2] ==> i1 == i2)]
#[requires(forall<i> 0 <= i && i < s.len() ==> 0 <= s[i] && s[i] < n)]
#[requires(0 <= k && k <= s.len())]
#[ensures(k == card(0, n, |j| exists<i> 0 <= i && i < k && s[i] == j))]
#[variant(k)]
fn inj_aux(s: Seq<Int>, n: Int, k: Int) {
    pearlite! {
        if k > 0 {
            card_false(0, n, |j| exists<i> i == k - 1 && s[i] == j);
            card_ge_2(0, n, |j| exists<i> i == k - 1 && s[i] == j);
            proof_assert!(card(0, n, |j| exists<i> i == k - 1 && s[i] == j) == 1);
            inj_aux(s, n, k - 1);
            card_disjoint(0, n,
                |j| exists<i> 0 <= i && i < k - 1 && s[i] == j,
                |j| exists<i> i == k - 1 && s[i] == j,
                |j| exists<i> 0 <= i && i < k && s[i] == j,
            );
        }
    }
}

#[logic(opaque)]
#[requires(forall<j> 0 <= j && j < n ==> (|k| exists<i> 0 <= i && i < s.len() && s[i] == k)[j])]
#[ensures(s.surjective_onto(n))]
fn inj_helper(s: Seq<Int>, n: Int) {}

/*
    count and theorems
*/

impl<T> Seq<T> {
    /// Counts the number of occurences of `t` in
    /// `self` within the index range `a..b`.
    #[logic(open)]
    #[requires(a <= b)]
    #[ensures(0 <= result && result <= b - a)]
    pub fn count(self, a: Int, b: Int, t: T) -> Int {
        card(a, b, |i| self[i] == t)
    }

    /// Two sequences that are equal on the range `a..b`
    /// have the same counts on this range.
    #[logic(opaque)]
    #[requires(a <= b)]
    #[requires(forall<i> a <= i && i < b ==> self[i] == other[i])]
    #[ensures(self.count(a, b, t) == other.count(a, b, t))]
    pub fn count_congr(self, other: Self, a: Int, b: Int, t: T) {
        card_congr(a, b, |i| self[i] == t, |i| other[i] == t);
    }

    /// Chasles's relation for [`Seq::count`].
    #[logic(opaque)]
    #[requires(a <= b && b <= c)]
    #[ensures(self.count(a, c, t) == self.count(a, b, t) + self.count(b, c, t))]
    pub fn count_join(self, a: Int, b: Int, c: Int, t: T) {
        card_join(a, b, c, |i| self[i] == t);
    }
}

/*
    permutation_of and theorems
*/

impl<T> Seq<T> {
    /// true if and only if `other` is a permutation of `self`, which is
    /// defined as having the same length and the same element counts.
    /// This definition makes it trivially an equivalence relation.
    #[logic(open)]
    pub fn permutation_of(self, other: Self) -> bool {
        pearlite! {
            self.len() == other.len() &&
            forall<t> self.count(0, self.len(), t) == other.count(0, other.len(), t)
        }
    }

    /// If `other` is obtained from `self` by swapping two elements,
    /// then it is a permutation of `self`.
    #[logic(opaque)]
    #[requires(self.exchange(other, i, j))]
    #[ensures(self.permutation_of(other))]
    pub fn permutation_of_exchange(self, other: Self, i: Int, j: Int) {
        |t: T| {
            if i < j {
                self.count_join(0, i, i + 1, t);
                self.count_join(0, i + 1, j, t);
                self.count_join(0, j, j + 1, t);
                self.count_join(0, j + 1, self.len(), t);
                self.count_congr(other, 0, i, t);
                self.count_congr(other, i + 1, j, t);
                self.count_congr(other, j + 1, self.len(), t);
                proof_assert!(self.count(0, self.len(), t) == other.count(0, other.len(), t));
            } else if j < i {
                self.count_join(0, j, j + 1, t);
                self.count_join(0, j + 1, i, t);
                self.count_join(0, i, i + 1, t);
                self.count_join(0, i + 1, self.len(), t);
                self.count_congr(other, 0, j, t);
                self.count_congr(other, j + 1, i, t);
                self.count_congr(other, i + 1, self.len(), t);
                proof_assert!(self.count(0, self.len(), t) == other.count(0, other.len(), t));
            } else {
                self.count_join(0, i, i + 1, t);
                self.count_join(0, i + 1, self.len(), t);
                self.count_congr(other, 0, i, t);
                self.count_congr(other, i + 1, self.len(), t);
                proof_assert!(self.count(0, self.len(), t) == other.count(0, other.len(), t));
            }
        };
    }

    /// Bijectively reindexing a sequence yields a permutation.
    #[logic(opaque)]
    #[requires(idx.len() == other.len())]
    #[requires(idx.injective_into(self.len()) && idx.surjective_onto(self.len()))]
    #[requires(forall<i> 0 <= i && i < idx.len() ==> other[i] == self[idx[i]])]
    #[ensures(self.permutation_of(other))]
    pub fn permutation_of_reindex(self, other: Seq<T>, idx: Seq<Int>) {
        pearlite! {
            idx.length_bij(self.len());
            |t: T| {
                permutation_of_reindex_aux(self, other, idx, t, idx.len());
                |k| if 0 <= k && k < self.len() { permutation_of_reindex_helper(self, idx, t, k); };
                card_congr(0, self.len(),
                    |j| self[j] == t && exists<i> 0 <= i && i < idx.len() && idx[i] == j,
                    |j| self[j] == t
                );
                proof_assert!(self.count(0, self.len(), t) == other.count(0, other.len(), t));
            };
        }
    }

    /// A permutation can always be seen as a bijective reindexing.
    #[logic(opaque)]
    #[requires(self.permutation_of(other))]
    #[ensures(result.len() == other.len())]
    #[ensures(result.injective_into(self.len()) && result.surjective_onto(self.len()))]
    #[ensures(forall<i> 0 <= i && i < result.len() ==> other[i] == self[result[i]])]
    pub fn reindex_of_permutation(self, other: Seq<T>) -> Seq<Int> {
        let res = Seq::create(other.len(), |i| {
            if 0 <= i && i < other.len() {
                extract_indices(self, other[i], self.len())[get_indices_in_class(other)[i]]
            } else {
                0
            }
        });
        proof_assert!(res.injective_into(self.len()));
        res.surj_of_inj(self.len());
        res
    }
}

//private lemmas
#[logic(opaque)]
#[requires(idx.len() == s2.len())]
#[requires(idx.injective_into(s1.len()))]
#[requires(forall<i> 0 <= i && i < idx.len() ==> s2[i] == s1[idx[i]])]
#[requires(0 <= k && k <= idx.len())]
#[ensures(s2.count(0, k, t) == card(0, s1.len(), |j| s1[j] == t && exists<i> 0 <= i && i < k && idx[i] == j))]
#[variant(k)]
fn permutation_of_reindex_aux<T>(s1: Seq<T>, s2: Seq<T>, idx: Seq<Int>, t: T, k: Int) {
    pearlite! {
        if k > 0 {
            permutation_of_reindex_aux(s1, s2, idx, t, k - 1);
            let p = |j| s1[j] == t && idx[k - 1] == j;
            card_disjoint(0, s1.len(),
                |j| s1[j] == t && exists<i> 0 <= i && i < k - 1 && idx[i] == j, p,
                |j| s1[j] == t && exists<i> 0 <= i && i < k && idx[i] == j,
            );
            card_false(0, s1.len(), p);
            if s2[k - 1] == t {
                card_ge_2(0, s1.len(), p);
                proof_assert!(card(0, s1.len(), p) == 1);
            } else {
                proof_assert!(card(0, s1.len(), p) == 0);
            }
        } else {
            card_false(0, s1.len(), |j| s1[j] == t && exists<i> 0 <= i && i < k && idx[i] == j);
        }
    }
}

#[logic(opaque)]
#[requires(idx.surjective_onto(s1.len()))]
#[requires(0 <= k && k < s1.len())]
#[ensures(
    (|j| s1[j] == t && exists<i> 0 <= i && i < idx.len() && idx[i] == j)[k] ==
    (|j| s1[j] == t)[k]
)]
fn permutation_of_reindex_helper<T>(s1: Seq<T>, idx: Seq<Int>, t: T, k: Int) {}

#[logic(opaque)]
#[requires(0 <= i && i <= s.len())]
#[ensures(forall<j> 0 <= j && j < result.len() ==> 0 <= result[j] && result[j] < i && s[result[j]] == t)]
#[ensures(result.len() == s.count(0, i, t))]
#[ensures(forall<j, k> 0 <= j && j < k && k < result.len() ==> result[j] < result[k])]
#[variant(i)]
fn extract_indices<T>(s: Seq<T>, t: T, i: Int) -> Seq<Int> {
    if i == 0 {
        seq![]
    } else {
        let prev = extract_indices(s, t, i - 1);
        if s[i - 1] == t { prev.snoc(i - 1) } else { prev }
    }
}

#[logic(opaque)]
#[ensures(result.len() == s.len())]
#[ensures(forall<j> 0 <= j && j < result.len() ==> 0 <= result[j] && result[j] < s.count(0, s.len(), s[j]))]
#[ensures(forall<j, k> 0 <= j && j < k && k < result.len() ==> s[j] == s[k] ==> result[j] < result[k])]
fn get_indices_in_class<T>(s: Seq<T>) -> Seq<Int> {
    |i| {
        if 0 <= i && i < s.len() {
            s.count_join(0, i + 1, s.len(), s[i]);
            proof_assert!(s.count(0, i, s[i]) < s.count(0, s.len(), s[i]));
        }
    };
    Seq::create(s.len(), |i| if 0 <= i { s.count(0, i, s[i]) } else { 0 })
}
