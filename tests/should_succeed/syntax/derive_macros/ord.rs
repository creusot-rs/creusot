#![allow(dead_code)]

extern crate creusot_std;
use creusot_std::{
    prelude::*,
    std::cmp::{Eq, Ord, PartialEq, PartialOrd},
};

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct UnitStruct;

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct PublicNamedStruct {
    pub foo: u32,
    pub bar: u64,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct PrivateNamedStruct {
    foo: u32,
    bar: u64,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct Newtype(u32);

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct PublicTupleStruct(pub u32, pub u64);

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct PrivateTupleStruct {
    foo: u32,
    bar: u32,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct ManyFields {
    a: u32,
    b: u32,
    c: u32,
    d: u32,
    e: u32,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct LargeTupleStruct(u32, u32, u32, u32);

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum CLikeEnum {
    Foo,
    Bar,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum CLikeEnumWithInitialDiscriminant {
    Foo = 42,
    Bar,
}

pub fn c_like_enum_with_initial_discriminant() {
    proof_assert!(
        CLikeEnumWithInitialDiscriminant::Foo.deep_model()
            < CLikeEnumWithInitialDiscriminant::Bar.deep_model()
    );
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum CLikeEnumWithAllDiscriminants {
    Foo = 42,
    Bar = 100,
}

pub fn c_like_enum_with_all_discriminants() {
    proof_assert!(
        CLikeEnumWithAllDiscriminants::Foo.deep_model()
            < CLikeEnumWithAllDiscriminants::Bar.deep_model()
    );
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum CLikeEnumWithAllDiscriminantsReversed {
    Foo = 42,
    Bar = 5,
}

pub fn c_like_enum_with_all_discriminants_reversed() {
    proof_assert!(
        CLikeEnumWithAllDiscriminantsReversed::Foo.deep_model()
            > CLikeEnumWithAllDiscriminantsReversed::Bar.deep_model()
    );
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum CLikeEnumWithMixedDiscriminants {
    A = 42,
    B,
    C = 10,
    D,
}

pub fn c_like_enum_with_mixed_discriminants() {
    proof_assert!(
        CLikeEnumWithMixedDiscriminants::C.deep_model()
            < CLikeEnumWithMixedDiscriminants::D.deep_model()
    );
    proof_assert!(
        CLikeEnumWithMixedDiscriminants::D.deep_model()
            < CLikeEnumWithMixedDiscriminants::A.deep_model()
    );
    proof_assert!(
        CLikeEnumWithMixedDiscriminants::A.deep_model()
            < CLikeEnumWithMixedDiscriminants::B.deep_model()
    );
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum TupleEnum {
    Foo(u32),
    Bar(u64),
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum NamedEnumSingleField {
    Foo { foo: u32 },
    Bar { bar: u64 },
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum NamedEnumMultipleFields {
    Foo { foo: u32, bar: i8 },
    Bar { foo: u64, bar: u16, baz: char },
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum ManyFieldsEnum {
    A(u32, u32, u32, u32),
    B(u32, u32, u32, u32, u32),
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum ReverseFieldCountEnum {
    A { a: u32, b: u32, c: u32 },
    B { a: u32 },
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum MixedEnum {
    Foo(u32),
    Bar { foo: u32, bar: i16 },
    Baz,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum ReverseMixedEnum {
    Empty,
    One(u32),
    Two(u32, u32),
    AnotherEmpty,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct GenericStruct<T> {
    first: T,
    second: T,
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub enum GenericEnum<T> {
    A(T),
    B { first: T, second: T },
}

#[derive(Eq, PartialEq, Ord, PartialOrd, DeepModel)]
#[DeepModelTy(derive(OrdLogic, PartialOrdLogic))]
pub struct MultipleGenerics<A, B, C> {
    a: A,
    b: B,
    c: C,
}

#[derive(OrdLogic, PartialOrdLogic)]
pub struct SimpleDeepModelTy {
    pub x: Int,
    pub y: Int,
}

// Straightforward implementation - NOT what DeepModel derives
#[derive(OrdLogic, PartialOrdLogic)]
pub struct DeepModelTyWithGenerics<T> {
    pub x: T,
    pub y: T,
}

// What DeepModel derives
#[derive(OrdLogic, PartialOrdLogic)]
#[DeepModelTy]
pub struct DeepModelTyWithGenericsAsDerivedByMacro<T: DeepModel> {
    pub x: <T as DeepModel>::DeepModelTy,
    pub y: <T as DeepModel>::DeepModelTy,
}
