extern crate creusot_contracts;
use creusot_contracts::*;

struct UnionFind {
    // The real data of our union find
    data: Vec<usize>,
    // a ghost array of distance for each node to its root element
    dist: Snapshot<Seq<Int>>,
}

impl UnionFind {
    // This invariant captures well-formed union find forests
    #[predicate]
    fn inv(self) -> bool {
        pearlite! { 
            // Needed to ensure that each element has a distance and vice-versa
            (self.data@.len() == self.dist.len()) &&
            // All data elements are well-formed
            (forall<i : _> 0 <= i && i < self.data@.len() ==> self.data[i]@ < self.data@.len()) &&
            // Distances are monotone decreasing and non-negative
            (forall<i : _> 0 <= i && i < self.dist.len() ==> {
                (self.data[i]@ == i && self.dist[i] == 0) 
                // This expression is the most important in the whole file.
                // By ensuring that the distance value is either 0 for root nodes or *decreasing* (but not necessarily n - 1!!)
                // we capture exactly the right amount of detail needed to prove `union` and `repr`. 
                || (self.dist[self.data[i]@] < self.dist[i] && self.dist[i] > 0)
            })
        } 
    }

    #[logic]
    // Logic functions are mathematical and thus must be *total*, so we prove termination.
    // Here we leverage the fact that the distance of a node is a well-founded relation (decreasing finite chain)
    #[variant(self.dist[ix])]
    // To prove the variant we need to know our distances are well-formed so we require the invariant to hold
    #[requires(self.inv())]
    // Since `ix` is an int we must require it to be non-negative, and in bounds
    #[requires(ix >= 0)]
    #[requires(ix < self.dist.len())]
    #[ensures(result@ < self.dist.len())]
    #[ensures(self.dist[result@] == 0)] // Not sure if this is really necessary
    fn repr(self, ix: Int) -> usize {
        if self.data[ix].shallow_model() == ix {
            self.data[ix] 
        } else {
            // `shallow_model` is what `@` desugars to. Can be useful when you don't want to wrap things in `pearlite! {..}`
            self.repr(self.data[ix].shallow_model())
        }
    }

    #[ensures(result.inv())]
    fn new(n: usize) -> Self {
        let mut dist = snapshot! { Seq::EMPTY };
        let mut data = Vec::new();

        // Unfortunately, we don't have a good way to create a sequence of length `n`, so we use a loop.
        // `produced` is a keyword available when dealing w for-loops that holds the sequence of values
        // already produced by the iteration. 
        #[invariant(data@ == *produced)]
        #[invariant(dist.len() == data@.len())]
        #[invariant(forall<i : _> 0 <= i && i < dist.len() ==> dist[i] == 0)]
        for ix in 0..n {
            data.push(ix);
            dist = snapshot! {dist.push(0)};
            // We need to this to prove `dist@ == *produced` since provers are not good at *extensional* reasoning. 
            // aka even if two sequences are equal at every point, a prover might not be able to prove that they are equal.
            // `ext_eq` has a spec which says exactly that fact. 
            proof_assert!(data@.ext_eq(*produced));
        }

        UnionFind {
            data,
            dist,
        }
    }

    // `find` is basically just a Rust version of `repr` (as seen by its postcondition).
    // This is a common pattern in verification: write a simple mathematical version of the operation, prove things about it
    // then show that a program version refines it. 
    #[requires(self.inv())]
    #[requires(a@ < self.data@.len())]
    // note we don't need to say anything about `result` beyond its correspondence to `repr` since thats all implied by `repr`
    #[ensures(result == self.repr(a@))]
    fn find(&self, a: usize) -> usize {
         if self.data[a] == a {
            a 
        } else {
            self.find(self.data[a])
        }
    }

    #[logic]
    #[requires(self.inv())]
    #[requires(a < self.data@.len())]
    #[ensures(self.repr(a) == self.repr(self.data[a]@))]
    fn repr_parents(self, a : Int) {

    }

    #[logic]
    #[requires(self.inv())]
    #[requires(rhs.inv())]
    #[requires(a < self.data@.len())]
    #[requires(self.dist == rhs.dist)]
    #[requires(forall<i : _> 0 <= i && i <self.data@.len()
            ==> self.dist[i] <= self.dist[a] ==>
            self.data[i] == rhs.data[i]
    )]
    #[ensures(self.repr(a) == rhs.repr(a))]
    #[variant(self.data[a]@)]
    fn repr_frame(self, rhs: Self, a : Int)  {
        if self.data[a].shallow_model() == a {
            ()
        } else {
            self.repr_frame(rhs, self.data[a].shallow_model())
        }
    }

    // `find` is basically just a Rust version of `repr` (as seen by its postcondition).
    // This is a common pattern in verification: write a simple mathematical version of the operation, prove things about it
    // then show that a program version refines it.
    #[requires(self.inv())]
    #[requires(a@ < self.data@.len())]
    // note we don't need to say anything about `result` beyond its correspondence to `repr` since thats all implied by `repr`
    #[ensures(result == self.repr(a@))]
    #[ensures((^self).data@.len() == self.data@.len())]
    #[ensures((^self).inv())]
    #[ensures(forall<i : _> 0 <= i && i < self.data@.len() ==> self.repr(i) == (^self).repr(i))]
    fn find_mut(&mut self, a: usize) -> usize {
        let old_self = snapshot!(*self);
        let grandparent = self.data[self.data[a]];
        if a == grandparent {
            a
        } else {
            let repr = snapshot!(self.repr(a@));
            proof_assert!(self.repr(grandparent@) == self.repr(a@));
            self.data[a] = grandparent;
            proof_assert!(self.data@ == old_self.data@.set(a@, grandparent));
            proof_assert!(self.repr(a@) == self.repr(grandparent@));

            proof_assert!(self.repr(a@) == old_self.repr(a@));
            proof_assert!(forall<i : _> 0 <= i && i < self.data@.len() ==> old_self.repr(i) == self.repr(i));
            let res = self.find_mut(grandparent);
            proof_assert!(*repr == self.repr(a@));
            proof_assert!(self.repr(grandparent@) == self.repr(a@));
            proof_assert!(forall<i : _> 0 <= i && i < self.data@.len() ==> old_self.repr(i) == self.repr(i));
            res
        }
    }


    #[requires(self.inv())]
    #[requires(a@ < self.data@.len())]
    #[requires(b@ < self.data@.len())]
    #[ensures((^self).inv())]
    fn union(&mut self, a: usize, b: usize) {
        let a_repr = self.find(a);
        let b_repr = self.find(b);

        if a_repr == b_repr {
            return;
        }
        // We want to set `b_repr -> a_repr`, this will break the distance invariant. 
        // Before we can update `b_repr` we need to "make space" in the distance relation. 
        // The fact our relation only uses `<` allows us to do that. 
        self.dist = snapshot! { self.increment(b_repr) };
        // proof_assert! { self.inv() };
        self.data[b_repr] = a_repr;
        // Now we can set our distance and close things out.
        self.dist = snapshot! { self.dist.set(b_repr@, 1) };
        // proof_assert! { self.dist[a_repr@] == 0 };
    }

    // See the comment on the unfolded `helper` version below
    #[logic]
    #[requires(self.inv())]
    #[requires(b@ < self.data@.len())]
    #[ensures(result.len() == self.dist.len())]
    #[ensures(
        forall<i : _> 0 <= i && i < result.len() ==> 
            if self.repr(i) == b { result[i] == self.dist[i] + 1 } else { result[i] == self.dist[i]}
    )]
    fn increment(self, b: usize) -> Seq<Int> {
        self.increment_helper(b, self.dist.len())
    }

    // This function iterates over the whole `dist` array and adds 1 to all children of `b`. 
    // This is a slight improvement over the version in the video, it turns out we don't need to avoid the `b` case if we 
    // `increment` before updating the parent pointer.
    // `increment_helper(self, b, cur) updates `dist[..cur]`, so `cur` is an upper-excluded bound
    #[logic]
    // `cur` wf
    #[requires(cur >= 0)]
    #[requires(cur <= self.data@.len() )]
    // We need this to call `repr`
    #[requires(self.inv())]
    // `b` wf
    #[requires(b@ < self.data@.len())]
    #[ensures(result.len() == cur)]
    // Children of `b` are updated, all others unchanged.
    #[ensures(
        forall<i : _> 0 <= i && i < result.len() ==> 
            if self.repr(i) == b { result[i] == self.dist[i] + 1 } else { result[i] == self.dist[i]}
    )]
    // A recursive logical function needs a variant.
    #[variant(cur)]
    fn increment_helper(self, b: usize, cur: Int) -> Seq<Int> {
        // `self.dist[..0] == EMPTY`
        if cur == 0 { 
            Seq::EMPTY
        } else {
            // Classic source of off-by-ones, we need to consistently use `cur - 1`
            let cur_dist = if self.repr(cur - 1) == b {
                self.dist[cur - 1] + 1
            } else {
                self.dist[cur - 1]
            };
            let pre = self.increment_helper(b, cur - 1) ;

            pre.push(cur_dist)           
        }
    }

}   