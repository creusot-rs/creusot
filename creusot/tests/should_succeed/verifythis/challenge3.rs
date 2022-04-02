extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

struct HSet<T> { inner: Vec<Option<T>> } 

trait Hash {
    #[ensures(result < state)]
    fn hash(&self, state: usize) -> usize;
}



impl<T: Hash + Eq> HSet<T> {
    #[predicate]
    fn all_none(&self) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.inner).len() ==>
                (@self.inner)[i] === None
        }
    }
    #[predicate]
    fn full(&self, hash: usize) -> bool {
        pearlite! {
            forall<i: Int> 0 <= i && i < (@self.inner).len() ==>
                !((@self.inner)[(i + @hash) % (@self.inner).len()] === None)
        }
    }

    #[ensures((@result.inner).len() === @n)]
    #[ensures(result.all_none())]
    pub fn empty(n: usize) -> Self {
        let mut v: Vec<Option<T>> = Vec::new();
        let mut i: usize = 0;
        #[invariant(len_ok, @i <= @n)]
        #[invariant(len_is, @i === (@v).len())]
        #[invariant(all_none, forall<j: Int> 0 <= j && j < @i ==>
            (@v)[j] === None
        )]
        while i < n {
            v.push(None);
            i += 1;
        }
        HSet { inner: v }
    }
    
    #[ensures(@result === (@self.inner).len())]
    fn len(&self) -> usize {
        return self.inner.len()
    }

    pub fn member(&self, k: T) -> bool {
        let n = self.inner.len();

        let i0 = k.hash(n);
        let mut i : usize = 0;

        #[invariant(i_loop, @i < @n)]
        loop {
            let k1 = &self.inner[i]; // atomic_load
            match k1 {
                Some(k2)=>  { if k2.eq(&k) { return true } }
                _ => return false,
            }
            i = (i + 1) % n;
            if i == i0 {
                break
            }
        }
        
        return false;
    }
    
    #[requires((@self.inner).len() < @usize::MAX/2)]
    #[ensures((!result) ==> ((exists<i : _> self.full(i)) && self.resolve()))]
    #[ensures(result ==> exists<i : Int> (@(^self).inner)[i] == Some(key_in))]
    fn insert(&mut self, key_in: T) -> bool {
        let old_self = Ghost::record(&self);
        let n: usize = self.len();
        let hash: usize = key_in.hash(n);
        let mut i: usize = 0;
        let key = Some(key_in);
        #[invariant(i_ok, @i <= (@self.inner).len())]
        #[invariant(neq, @n === (@self.inner).len())]
        #[invariant(inv, forall<j: Int> 0 <= j && j < @i ==>
            !((@self.inner)[(j + @hash)%(@self.inner).len()] === key)
        )]
        #[invariant(inv2, forall<j: Int> 0 <= j && j < @i ==>
            !((@self.inner)[(j + @hash)%(@self.inner).len()] === None)
        )]
        #[invariant(unch, @old_self === self)]
        #[invariant(proph, ^@old_self === ^self)]
        while i < self.len() {
            match &self.inner[(i+hash)%n] {
            None  => { 
                 self.inner[(i+hash)%n] = key;
                    return true;
            }
            a@Some(_) => { if a.eq(&key) { return true } },
            }
            i += 1;
        }
        return false;
    }
}