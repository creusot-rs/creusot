#![allow(dead_code)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(DeepModel)]
#[DeepModelTy(derive(PartialOrdLogic))]
#[DeepModelTy = "Derived"]
#[DeepModelTy(derive(OrdLogic))]
pub struct Deriving;

pub struct Derived;
