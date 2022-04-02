extern crate creusot_contracts;
use creusot_contracts::*;
use creusot_contracts::std::*;

struct HSet<T> { inner: Vec<Option<T>> } 

trait Hash {
    // Range 0 to n
    fn hash(&self, state: usize) -> usize;
}

#[trusted]
fn compare_and_swap<T>(el: &T, inv: &T, key: &T) -> T {
    std::process::abort()
}

impl<T: Hash + Eq> HSet<T> {
    // #[ensures((@self.inner).len() === @n)]
    pub fn empty(n: usize) -> Self {
        let mut v  = Vec::new();
        let mut i: usize = 0;
        // #[invariant(len_ok, @i <= @n)]
        while i < n {
            v.push(None);
            i += 1;
        }
        HSet { inner: v }
    }
    
    fn len(&self) -> usize {
        0
    }

    pub fn member(&self, k: T) -> bool {
        let n = self.inner.len();

        let i0 = k.hash(n);
        let mut i = 0;

        loop {
            let k1 = &self.inner[i]; // atomic_load
            match k1 {
                Some(k2)=>  { if k2.eq(&k) { return true } }
                _ => return false,
            }
            i += (i + 1) % n;
            if i == i0 {
                break
            }
        }
        
        return false;
    }
    
    fn insert(&self, key: T) -> bool {
        let n: usize = self.len();
        let mut i: usize = key.hash(n);
        let i_start = i;
        let key = Some(key);
        #[invariant(i_ok, @i < @n)]
        loop {
            /* // OPT
            kk: Key = atomic_load(self[i]);
            match kk {
                key => return true;
                None => {
                    break;
                } // Spot taken, take next
                _ => {
                    i = (i + 1) % n
                    if i == i_start {
                        return false;
                    }
                }

            }

            */
            let none = None;
            let other_key = compare_and_swap(&self.inner[i],&none, &key);
            if other_key.eq(&key) {
                return true;
            }
            i = (i + 1) % n;

            if i == i_start {
                return false
            }
        }
    }
}


