#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]
#![feature(type_ascription)]

extern crate creusot_contracts;

use creusot_contracts::*;

enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}
impl<T> WellFounded for List<T> {}

use List::*;

impl<T> List<T> {
    // This is sucky because why3 won't automatically attempt to rewrite using the `def` axiom
    #[pure]
    #[ensures(result >= 0)]
    #[variant(*self)]
    fn len(&self) -> Int {
        match self {
            Cons(_, ls) => Int::from(1) + ls.len(),
            Nil => 0.into(),
        }
    }

    logic! {
      fn get(self, ix: Int) -> Option<T> {
        match self {
          Cons(hd, tl) => {
            if ix == 0 {
              Some(hd)
            } else {
              tl.get(ix - 1)
            }
          },
          Nil => None
        }

      }
    }

    logic! {
      fn push(self, v: T) -> Self {
        match self {
          Cons(h, tl) => Cons(h, Box::new(tl.push(v))),
          Nil => Cons(v, Box::new(Nil)),
        }
      }
    }

    #[pure]
    #[requires(0 <= ix && ix < self.len())]
    #[ensures(Some(result) === self.get(ix))]
    #[variant(self)]
    fn index(self, ix: Int) -> T {
        match self {
            Cons(x, ls) => {
                if ix == Int::from(0) {
                    x
                } else {
                    ls.index(ix - Int::from(1))
                }
            }
            Nil => unreachable!("invalid index"),
        }
    }
}

logic! {
  fn as_ref<'a, T>(opt: Option<&T>) -> &'a Option<T> {
    match opt {
      Some(r) => &Some(*r),
      None => &None,
    }
  }
}

struct MyVec<T>(Vec<T>);

pub struct GhostRecord<T>
where
    T: ?Sized;

impl<T> GhostRecord<T> {
    logic! {
        #[trusted]
        fn model(self) -> T {
            panic!("GhostRecord model")
        }
    }

    #[trusted]
    #[ensures(result.model() === *a)]
    fn record(a: &T) -> GhostRecord<T> {
        GhostRecord::<T>
    }
}

impl<T> MyVec<T> {
    logic! {
      #[trusted]
      fn model(self) -> List<T> {
        Nil // Dummy value
      }
    }

    #[trusted]
    #[ensures(result.into() === self.model().len())]
    fn len(&self) -> usize {
        self.0.len()
    }

    #[trusted]
    #[ensures(*as_ref(result) === self.model().get(ix.into()))]
    fn get(&self, ix: usize) -> Option<&T> {
        self.0.get(ix)
    }

    #[trusted]
    #[ensures((^self).model() === (*self).model().push(v))]
    fn push(&mut self, v: T) {
        self.0.push(v)
    }

    #[trusted]
    #[requires(Int::from(ix) < self.model().len())]
    #[ensures(*result === self.model().index(ix.into()))]
    fn index(&self, ix: usize) -> &T {
        use std::ops::Index;
        self.0.index(ix)
    }

    #[trusted]
    #[requires(Int::from(ix) < self.model().len())]
    #[ensures(*result === (*self).model().index(ix.into()))]
    #[ensures(^result === (^self).model().index(ix.into()))]
    #[ensures(forall<j : Int> 0 <= j && j <= (^self).model().len() ==>
      !(j === ix.into()) ==>
      (^self).model().index(j) === (* self).model().index(j))]
    #[ensures(self.model().len() === (^self).model().len())]
    fn index_mut(&mut self, ix: usize) -> &mut T {
        use std::ops::IndexMut;
        self.0.index_mut(ix)
    }
}

#[ensures(forall<i : Int> 0 <= i && i < (^v).model().len() ==> (^v).model().index(i) === 0u32)]
#[ensures((*v).model().len() === (^v).model().len())]
fn all_zero(v: &mut MyVec<u32>) {
    let mut i = 0;
    let old_v: GhostRecord<&mut MyVec<u32>> = GhostRecord::record(&v);
    // This invariant is because why3 can't determine that the prophecy isn't modified by the loop
    // Either Why3 or Creusot should be improved to do this automaticallly (probably why3)
    #[invariant(proph_const, ^ v === ^ (old_v.model() : &mut _))]
    #[invariant(in_bounds, v.model().len() ===  (old_v.model() : &mut MyVec<u32>).model().len())]
    #[invariant(all_zero, forall<j : Int> 0 <= j && j < i.into() ==> v.model().index(j) === 0u32)]
    while i < v.len() {
        *v.index_mut(i) = 0;
        i += 1;
    }
}

fn main() {}
