extern crate creusot_contracts;
use creusot_contracts::Default;

#[derive(Default)]
pub struct Unit;

#[derive(Default)]
pub struct Tuple(pub i32, pub i64);

#[derive(Default)]
pub struct Named<T> {
    pub x: i32,
    pub y: T,
}

#[derive(Default)]
pub enum EUnit {
    X,
    #[default]
    Y,
}

#[derive(Default)]
pub enum ETuple {
    #[default]
    A(i32, i32),
    B {
        x: Vec<i32>,
    },
}

#[derive(Default)]
pub enum ENamed<T, U> {
    #[default]
    A {
        x: T,
        y: U,
    },
    B,
}
