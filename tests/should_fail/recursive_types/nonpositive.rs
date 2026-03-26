#![allow(unused)]
extern crate creusot_std;
use creusot_std::prelude::*;

mod opaque {
    pub struct AbstractBox<T>(Box<T>);
}

enum SemiopaqueOption<T> {
    None,
    Some(opaque::AbstractBox<T>),
}

pub struct Bad(SemiopaqueOption<Bad>);
