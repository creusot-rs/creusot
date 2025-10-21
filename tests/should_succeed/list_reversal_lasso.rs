#![allow(dead_code)]

extern crate creusot_contracts;

use creusot_contracts::{logic::ops::IndexLogic, prelude::*};
use std::ops::{Index, IndexMut};

/* Memory model */

struct Memory(pub Vec<Ptr>);
type Ptr = usize;

pub const NULL: Ptr = usize::MAX;

impl IndexLogic<Ptr> for Memory {
    type Item = Ptr;

    #[logic]
    fn index_logic(self, i: Ptr) -> Ptr {
        pearlite! { self.0[i] }
    }
}

impl Index<Ptr> for Memory {
    type Output = Ptr;

    #[requires(self.nonnull_ptr(i))]
    #[ensures(*result == self.index_logic(i))]
    fn index(&self, i: Ptr) -> &Ptr {
        &self.0[i]
    }
}

impl IndexMut<Ptr> for Memory {
    #[requires(self.nonnull_ptr(i))]
    #[ensures(*result == (*self).index_logic(i))]
    #[ensures(^result == (^self).index_logic(i))]
    #[ensures(self.0@.len() == (^self).0@.len())]
    #[ensures(forall<j: Ptr> self.nonnull_ptr(j) && i != j ==> (^self).index_logic(j) == (*self).index_logic(j))]
    fn index_mut(&mut self, i: Ptr) -> &mut Ptr {
        &mut self.0[i]
    }
}

impl Memory {
    #[logic]
    pub fn nonnull_ptr(self, i: Ptr) -> bool {
        pearlite! { self.0@.len() <= usize::MAX@ && i@ < self.0@.len() }
    }

    #[logic]
    pub fn mem_is_well_formed(self) -> bool {
        pearlite! {
            forall<i: Ptr> self.nonnull_ptr(i) ==> self[i] == NULL || self.nonnull_ptr(self[i])
        }
    }
}

impl Memory {
    #[requires(self.mem_is_well_formed())]
    #[requires(l == NULL || self.nonnull_ptr(l))]
    pub fn list_reversal_safe(&mut self, mut l: Ptr) -> Ptr {
        let mut r = NULL;

        #[invariant(r == NULL || self.nonnull_ptr(r))]
        #[invariant(l == NULL || self.nonnull_ptr(l))]
        #[invariant(self.mem_is_well_formed())]
        while l != NULL {
            let tmp = l;
            l = self[l];
            self[tmp] = r;
            r = tmp;
        }
        return r;
    }

    #[logic]
    fn list_seg(self, first: Ptr, s: Seq<Ptr>, last: Ptr, l: Int, h: Int) -> bool {
        pearlite! {
            first == if h == l { last } else { s[l] } &&
            (forall<i> l <= i && i < h ==> self.nonnull_ptr(s[i]) && self[s[i]] == if i == h - 1 { last } else { s[i+1] }) &&
            (forall<i, j> l <= i && i < h && l <= j && j < h && i != j ==> s[i] != s[j])
        }
    }

    #[logic]
    pub fn list(self, first: Ptr, s: Seq<Ptr>) -> bool {
        pearlite! {
            self.list_seg(first, s, NULL, 0, s.len())
        }
    }

    #[requires(self.list(l, *s))]
    #[ensures((^self).list(result, s.reverse()))]
    pub fn list_reversal_list(&mut self, mut l: Ptr, s: Snapshot<Seq<Ptr>>) -> Ptr {
        let mut r = NULL;
        let mut n = snapshot! { 0 };

        #[invariant(0 <= *n && *n <= s.len())]
        #[invariant(self.list_seg(l, *s, NULL, *n, s.len()))]
        #[invariant(self.list_seg(r, s.reverse(), NULL, s.len()-*n, s.len()))]
        // #[variant(s.len() - *n)]
        while l != NULL {
            l = std::mem::replace(&mut self[l], std::mem::replace(&mut r, l));
            n = snapshot! { *n + 1 }
        }
        return r;
    }

    #[logic]
    pub fn loop_(self, first: Ptr, s: Seq<Ptr>) -> bool {
        pearlite! {
            self.list_seg(first, s, s[0], 0, s.len())
        }
    }

    #[requires(s.len() > 0)]
    #[requires(self.loop_(l, *s))]
    #[ensures((^self).loop_(result, s.subsequence(1, s.len()).reverse().push_front(s[0])))]
    pub fn list_reversal_loop(&mut self, mut l: Ptr, s: Snapshot<Seq<Ptr>>) -> Ptr {
        let mut r = NULL;
        let mut n = snapshot! { 0 };

        #[invariant(0 <= *n && *n <= s.len() + 1)]
        #[invariant(*n == s.len() + 1 ==>
            l == NULL && r == s[0] && self.nonnull_ptr(r) &&
            (*self)[r] == s[s.len()-1] &&
            self.list_seg(s[s.len()-1], s.reverse(), s[0], 0, s.len()-1))]
        #[invariant(*n <= s.len() ==> self.list_seg(l, *s, s[0], *n, s.len()))]
        #[invariant(*n <= s.len() ==> self.list_seg(r, s.reverse(), NULL, s.len()-*n, s.len()))]
        // #[variant(s.len() + 1 - *n)]
        while l != NULL {
            proof_assert! { *n == s.len() ==> l == s.reverse()[s.len() - 1] }
            l = std::mem::replace(&mut self[l], std::mem::replace(&mut r, l));
            n = snapshot! { *n + 1 }
        }

        proof_assert! { forall<i> 0 <= i && i < s.len() ==>
            s.subsequence(1, s.len()).reverse().push_front(s[0])[i] ==
        if i == 0 { s[0] } else { s.reverse()[i-1] } };
        return r;
    }

    #[logic]
    pub fn lasso(self, first: Ptr, s1: Seq<Ptr>, s2: Seq<Ptr>) -> bool {
        pearlite! {
            let mid = if s2.len() == 0 { s1[s1.len()-1] } else { s2[0] };
            s1.len() > 0 &&
            (forall<i, j> 0 <= i && i < s1.len() && 0 <= j && j < s2.len() ==> s1[i] != s2[j]) &&
            self.list_seg(first, s1, mid, 0, s1.len()) &&
            self.list_seg(mid, s2, s1[s1.len()-1], 0, s2.len())
        }
    }

    #[requires(self.lasso(l, *s1, *s2))]
    #[ensures((^self).lasso(result, *s1, s2.reverse()))]
    pub fn list_reversal_lasso(
        &mut self,
        mut l: Ptr,
        s1: Snapshot<Seq<Ptr>>,
        s2: Snapshot<Seq<Ptr>>,
    ) -> Ptr {
        let mut r = NULL;
        let mut n = snapshot! { 0 };

        #[invariant(0 <= *n && *n <= 2*s1.len() + s2.len())]
        #[invariant({
            let mid = if s2.len() == 0 { s1[s1.len()-1] } else { s2[0] };
            *n <= s1.len() ==>
            self.list_seg(l, *s1, mid, *n, s1.len()) &&
            self.list_seg(mid, *s2, s1[s1.len()-1], 0, s2.len()) &&
            self.list_seg(r, s1.reverse(), NULL, s1.len()-*n, s1.len())})]
        #[invariant(s1.len() < *n && *n <= s1.len() + s2.len() ==>
            self.list_seg(l, *s2, s1[s1.len()-1], *n-s1.len(), s2.len()) &&
            self.list_seg(r, s2.reverse(), s1[s1.len()-1], s1.len()+s2.len()-*n, s2.len()) &&
            self.list_seg(s1[s1.len()-1], s1.reverse(), NULL, 0, s1.len()))]
        #[invariant({
            let mid = if s2.len() == 0 { s1[s1.len()-1] } else { s2[s2.len()-1] };
            s1.len() + s2.len() < *n ==>
            self.list_seg(l, s1.reverse(), NULL, *n-s1.len()-s2.len(), s1.len()) &&
            self.list_seg(r, *s1, mid, 2*s1.len()+s2.len()-*n, s1.len()) &&
            self.list_seg(mid, s2.reverse(), s1[s1.len()-1], 0, s2.len())})]
        // #[variant(2*s1.len() + s2.len() - *n)]
        while l != NULL {
            l = std::mem::replace(&mut self[l], std::mem::replace(&mut r, l));
            n = snapshot! { *n + 1 }
        }
        return r;
    }

    #[logic]
    #[requires(0 <= i && i <= s.len())]
    #[ensures(match result {
        None => forall<j> i <= j && j < s.len() ==> s[j]@ != p,
        Some(j) => i <= j && j < s.len() && s[j]@ == p
    })]
    #[variant(s.len() - i)]
    fn find_ptr_in_seq(s: Seq<Ptr>, i: Int, p: Int) -> Option<Int> {
        pearlite! {
            if i == s.len() { None }
            else if s[i]@ == p { Some(i) }
            else { Self::find_ptr_in_seq(s, i+1, p) }
        }
    }

    #[logic]
    #[requires(0 <= n)]
    #[requires(forall<i> 0 <= i && i < s.len() ==> s[i]@ < n)]
    #[requires(forall<i, j> 0 <= i && i < s.len() && 0 <= j && j < s.len() && i != j ==> s[i] != s[j])]
    #[ensures(s.len() <= n)]
    #[ensures(result)]
    #[variant(n)]
    fn pigeon(s: Seq<Ptr>, n: Int) -> bool {
        pearlite! {
            if n == 0 { true }
            else {
                match Self::find_ptr_in_seq(s, 0, n-1) {
                    None => Self::pigeon(s, n-1),
                    Some(i) =>
                        match Self::find_ptr_in_seq(s, i+1, n-1) {
                            None => Self::pigeon(s.subsequence(0, i).concat(s.subsequence(i+1, s.len())), n-1),
                            Some(_) => true
                        }
                }
            }
        }
    }

    #[logic]
    #[requires(self.mem_is_well_formed())]
    #[requires(last == NULL || self.nonnull_ptr(last))]
    #[requires(self.list_seg(first, s, last, 0, s.len()))]
    #[ensures(match result {
        (s, None) => self.list(first, s),
        (s1, Some(s2)) => self.lasso(first, s1, s2)
    })]
    #[variant(self.0@.len() - s.len())]
    fn find_lasso_aux(self, first: Ptr, last: Ptr, s: Seq<Ptr>) -> (Seq<Ptr>, Option<Seq<Ptr>>) {
        pearlite! {
            if last == NULL { (s, None) }
            else {
                match Self::find_ptr_in_seq(s, 0, last@) {
                    None => {
                        if Self::pigeon(s, self.0@.len()) {
                            self.find_lasso_aux(first, self[last], s.push_back(last))
                        } else {
                            (s, None) /* Dummy */
                        }
                    },
                    Some(i) => (s.subsequence(0, i+1), Some(s.subsequence(i+1, s.len())))
                }
            }
        }
    }

    #[logic]
    #[requires(self.mem_is_well_formed())]
    #[requires(first == NULL || self.nonnull_ptr(first))]
    #[ensures(match result {
        (s, None) => self.list(first, s),
        (s1, Some(s2)) => self.lasso(first, s1, s2)
    })]
    pub fn find_lasso(self, first: Ptr) -> (Seq<Ptr>, Option<Seq<Ptr>>) {
        pearlite! {
             Self::find_lasso_aux(self, first, first, Seq::empty())
        }
    }
}
