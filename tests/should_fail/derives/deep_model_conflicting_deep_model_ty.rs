#![allow(dead_code)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(DeepModel)]
#[DeepModelTy = "Derived"]
#[DeepModelTy(derive(PartialOrdLogic))]
pub struct Deriving;

pub struct Derived;
