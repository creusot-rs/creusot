#![allow(dead_code)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[derive(DeepModel)]
pub struct UnitStruct;

#[derive(DeepModel)]
pub struct TupleStruct(i32, bool);

#[derive(DeepModel)]
pub struct Struct {
    x: i32,
    b: bool,
}

#[derive(DeepModel)]
pub struct TupleStructGenerics<T: DeepModel, U>(i32, T, U)
where
    U: DeepModel;

#[derive(DeepModel)]
pub struct StructGenerics<T: DeepModel, U>
where
    U: DeepModel,
{
    x: i32,
    t: T,
    u: U,
}

// FIXME: unsupported for now
// #[derive(DeepModel)]
// pub enum EmptyEnum {}

#[derive(DeepModel)]
pub enum UnitEnum {
    A,
    B,
}

#[derive(DeepModel)]
pub enum Enum {
    A,
    Int(i32),
    Bool { b: bool },
}

#[derive(DeepModel)]
pub enum EnumGenerics<T: DeepModel, U>
where
    U: DeepModel,
{
    A,
    Int(i32),
    T(T),
    U { u: U },
}
