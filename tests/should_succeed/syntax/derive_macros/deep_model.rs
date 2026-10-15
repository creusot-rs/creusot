#![allow(dead_code)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(DeepModel)]
pub struct UnitStruct;

#[derive(DeepModel)]
pub struct TupleStruct(pub i32, pub bool);

#[derive(DeepModel)]
pub struct Struct {
    pub x: i32,
    pub b: bool,
}

#[derive(DeepModel)]
pub struct TupleStructGenerics<T: DeepModel, U>(pub i32, pub T, pub U)
where
    U: DeepModel;

#[derive(DeepModel)]
pub struct StructGenerics<T: DeepModel, U>
where
    U: DeepModel,
{
    pub x: i32,
    pub t: T,
    pub u: U,
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

// Regression tests for visibility
mod visibility_regression {
    use creusot_std::prelude::*;

    #[derive(DeepModel)]
    pub(crate) enum CrateVisibleEnum {
        A,
    }

    #[derive(DeepModel)]
    pub(super) enum ParentVisibleEnum {
        A,
    }

    #[derive(DeepModel)]
    pub(self) enum SelfVisibleEnum {
        A,
    }

    #[derive(DeepModel)]
    pub(crate) struct CrateVisibleStruct;

    mod nested {
        use creusot_std::prelude::*;

        #[derive(DeepModel)]
        pub(in crate::visibility_regression) struct AncestorVisibleStruct {}
    }
}

#[derive(DeepModel)]
pub struct StructWithPrivField(u32);

#[derive(DeepModel)]
pub struct StructWithPubCrateField(pub(crate) u32);

mod encapsulation {
    use creusot_std::prelude::*;

    #[derive(DeepModel)]
    pub struct StructWithPubSuperField(pub(super) u32);
}
