extern crate creusot_contracts;
use creusot_contracts::*;

extern_spec! {
  mod std {
    mod clone {
      trait Clone {
        #[ensures(@result == @*self)]
        fn clone(&self) -> Self
          where Self : Model;
      }
    }
  }
}

pub fn omg() {
    let _ = vec![1; 4].clone();
}
