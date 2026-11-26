#![allow(dead_code)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(DeepModel)]
#[DeepModelTy(derive(DeepModel))]
pub struct Deriving;

#[derive(DeepModel)]
#[DeepModelTy]
pub struct Model;
