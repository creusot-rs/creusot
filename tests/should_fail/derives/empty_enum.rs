#![allow(dead_code)]

extern crate creusot_std;
use creusot_std::{
    prelude::*,
    std::cmp::{Eq, Ord, PartialEq, PartialOrd},
};

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic PartialOrdLogic))]
pub enum EmptyEnum {}
