extern crate creusot_std;
use creusot_std::prelude::*;

pub enum A {
    Cons(Box<A>),
    Nil,
}

impl DeepModel for A {
    type DeepModelTy = Int;
    #[logic(open)]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            A::Cons(a) => *a.deep_model() + 1,
            A::Nil => 0,
        }
    }
}
