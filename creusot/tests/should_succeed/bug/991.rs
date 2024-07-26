#![allow(dead_code)]
extern crate creusot_contracts;
use creusot_contracts::*;

pub struct Formula {
    vec: Vec<usize>,
    b: bool,
}

impl ShallowModel for Formula {
    type ShallowModelTy = (Seq<usize>, bool);

    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (self.vec.shallow_model(), self.b)
    }
}

impl Formula {
    #[ensures(self@ == self@)] // Just here for the model access
    fn love_and_hope(&self) {}
}
