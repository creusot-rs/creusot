#![allow(dead_code)]

extern crate creusot_std;

mod point {
    use creusot_std::{
        prelude::*,
        std::{clone::Clone, cmp::PartialEq},
    };

    #[derive(Clone, PartialEq, DeepModel)]
    #[use_DeepModel]
    pub struct Point {
        x: u32,
        y: u32,
    }
}

fn point_clone_equals(val: point::Point) {
    let cloned = val.clone();
    assert!(cloned == val);
}
