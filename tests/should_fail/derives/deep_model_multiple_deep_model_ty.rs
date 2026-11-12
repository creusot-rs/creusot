#![allow(dead_code)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(DeepModel)]
#[DeepModelTy = "Derived1"]
#[DeepModelTy = "Derived2"]
pub struct Deriving;

pub struct Derived1;
pub struct Derived2;
