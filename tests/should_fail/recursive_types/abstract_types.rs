#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

mod opaque {
    pub struct AbstractBox<T>(Box<T>);
}

pub struct Bad(opaque::AbstractBox<Bad>);
