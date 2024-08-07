extern crate creusot_contracts;
//use crate::Id;
use std::fmt::Debug;
use creusot_contracts::{std::clone::Clone, Snapshot, snapshot, proof_assert, invariant, ensures, variant, logic, logic::{ IndexLogic, FSet}, open, pearlite, predicate, requires, trusted, Int, Seq, ShallowModel, invariant::Invariant};

#[derive(/*Debug,*/ Clone)]
// #[cfg_attr(feature = "serde-1", derive(serde::Serialize, serde::Deserialize))]
pub struct UnionFind {
    parents: Vec<Id>,
    dist: Snapshot<Seq<Int>>,
}

type Id = u32;

impl UnionFind {

    #[logic]
    fn len(&self) -> Int {
        pearlite!{ self.parents@.len() }
    }

    #[predicate]
    #[requires(self.len() <= u32::MAX@)]
    fn invariant(&self) -> bool {
        pearlite! {
            (self.len() == self.dist.len())
            && forall<i: Int> 0 <= i && i < self.len() ==>
                self.parents[i]@ >= 0 && self.parents[i]@ < self.len()
            && forall <i: Int> 0 <= i && i < self.len() ==>
                (self.dist[i] == 0 && self.parents[i]@ == i)
                || (self.dist[i] > 0 && self.dist[self.parents[i]@] < self.dist[i])
        }
    }

    #[requires(self.len() < u32::MAX@)]
    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[ensures(result@ == self.len())]
    #[ensures((^self).parents[result@] == result)]
    #[ensures(self.len() + 1 == (^self).len())]
    pub fn make_set(&mut self) -> Id {
        // let id = Id::from(self.parents.len());
        let id = self.parents.len() as Id;
        self.parents.push(id);
        self.dist = snapshot!{ self.dist.push(0) }; //ghost code
        id
    }

    #[ensures(result@ == self.parents@.len())]
    pub fn size(&self) -> usize {
        self.parents.len()
    }

    #[requires(self.invariant())]
    #[requires(query@ < self.len())]
    #[ensures(result == self.parents@[query@])]
    fn parent(&self, query: Id) -> Id {
        //self.parents[usize::from(query)]
        self.parents[query as usize]
    }

    #[requires(query@ < self.len())]
    #[ensures((*self).parents@[query@] == *result)]
    #[ensures((^self).parents@[query@] == ^result)]
    #[ensures((*self).parents@.len() ==(^self).parents@.len())]
    #[ensures(forall<i: Int> 0 <= i && i != query@ && i < self.parents@.len() 
        ==> self.parents@[i] == (^self).parents@[i])]
    #[ensures(self.dist == (^self).dist)]
    fn parent_mut(&mut self, query: Id) -> &mut Id {
        &mut self.parents[query as usize]
    }

    #[logic]
    #[requires(self.invariant())]
    #[requires(i >= 0 && i < self.len())]
    #[ensures(result >= 0 && result < self.len())]
    #[variant(self.dist[i])]
    fn find_pure(&self, i: Int) -> Int { //same as repr function
        pearlite! {
            if self.parents@[i]@ == i {
                i
            } else {
                self.find_pure(self.parents@[i]@)
            }
        }
    }

    #[requires(self.invariant())]
    #[requires(current@ < self.len())]
    #[ensures(result@ < self.len())]
    #[ensures(result == self.parents@[result@])]
    #[ensures(result@ == self.find_pure(current@))]
    pub fn find(&self, mut current: Id) -> Id {
        let init_current = current; //ghost code
        #[invariant(
            current@ < self.len()
            && self.find_pure(init_current@) == self.find_pure(current@)
        )]
        while current != self.parent(current) {
            current = self.parent(current)
        }
        current
    }

    /*
    //TODO!
    // ensure none of the roots change
    // ensure path length is halved?
    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[requires(current@ < self.len())]
    #[ensures(self.len() == (^self).len())]
    pub fn find_mut(&mut self, mut current: Id) -> Id {
        let init_current = current; //ghost code
        #[invariant(
            current@ < self.len()
            && self.find_pure(init_current@) == self.find_pure(current@)
        )]
        while current != self.parent(current) {
            let grandparent = self.parent(self.parent(current));
            *self.parent_mut(current) = grandparent;
            current = grandparent;
        }
        current
    }

    #[logic]
    fn decr(&self, c: Int, n: Int) -> Seq<Int> {
        if n == 0 {
            Seq::EMPTY
        } else {
            //todo
        }
    }
    */

    #[requires(self.invariant())]
    #[ensures((^self).invariant())]
    #[requires(root1@ < self.len() && root2@ < self.len())]
    #[requires(self.parents@[root1@] == root1 && self.parents@[root2@] == root2 )]
    #[ensures((^self).parents@[root1@] == root1)]
    #[ensures((^self).parents@[root2@] == root1)]
    #[ensures((*self).len() == (^self).len())]
    #[ensures(forall<i: Int> 0 <= i && i != root2@ && i < self.len() 
        ==> self.parents@[i] == (^self).parents@[i])]
    /// Given two leader ids, unions the two eclasses making root1 the leader.
    pub fn union(&mut self, root1: Id, root2: Id) -> Id {
        //ghost code
        if root1 != root2 {
            self.dist = snapshot!{ self.incr(root2@, self.len()) };
        }

        *self.parent_mut(root2) = root1;
        root1
    }

    //rebuild all dists pointing to r with +1
    #[logic]
    #[requires(n >= 0 && n <= self.len())]
    #[requires(r >= 0 && r < self.len())]
    #[requires(self.invariant())]
    #[ensures(result.len() == n)]
    #[ensures(forall<i: Int> i >= 0 && i < result.len() ==>
        if self.find_pure(i) == r {
            result[i] == self.dist[i] + 1
        } else {
            result[i] == self.dist[i] 
        })]
    #[variant(n)]
    fn incr(&self, r: Int, n: Int) -> Seq<Int> {
        if n == 0 {
            Seq::EMPTY
        } else {
            let n_dist = if self.find_pure(n - 1) == r {
                self.dist[n - 1] + 1
            } else {
                self.dist[n - 1]
            };
            let dist = self.incr(r, n - 1);
            dist.push(n_dist)
        }
    }
}


// #[cfg(test)]
// mod tests {
//     use super::*;

//     fn ids(us: impl IntoIterator<Item = usize>) -> Vec<Id> {
//         us.into_iter().map(|u| u.into()).collect()
//     }

//     #[test]
//     fn union_find() {
//         let n = 10;
//         let id = Id::from;

//         let mut uf = UnionFind::default();
//         for _ in 0..n {
//             uf.make_set();
//         }

//         // test the initial condition of everyone in their own set
//         assert_eq!(uf.parents, ids(0..n));

//         // build up one set
//         uf.union(id(0), id(1));
//         uf.union(id(0), id(2));
//         uf.union(id(0), id(3));

//         // build up another set
//         uf.union(id(6), id(7));
//         uf.union(id(6), id(8));
//         uf.union(id(6), id(9));

//         // this should compress all paths
//         // for i in 0..n {
//         //     uf.find_mut(id(i));
//         // }

//         // indexes:         0, 1, 2, 3, 4, 5, 6, 7, 8, 9
//         let expected = vec![0, 0, 0, 0, 4, 5, 6, 6, 6, 6];
//         assert_eq!(uf.parents, ids(expected));
//     }
// }
