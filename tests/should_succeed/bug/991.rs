#![allow(dead_code)]
extern crate creusot_contracts;
use creusot_contracts::*;

pub struct Formula {
    vec: Vec<usize>,
    b: bool,
}

impl View for Formula {
    type ViewTy = (Seq<usize>, bool);

    #[logic]
    #[open(crate)]
    fn view(self) -> Self::ViewTy {
        (self.vec.view(), self.b)
    }
}

impl Formula {
    #[ensures(self@ == self@)] // Just here for the model access
    fn love_and_hope(&self) {}
}
