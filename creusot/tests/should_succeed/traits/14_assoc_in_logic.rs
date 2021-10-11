#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

trait Assoc {
    type Ty;
}

#[logic_rust]
#[trusted]
fn from_ty<T: Assoc>(x: T::Ty) -> T {
    panic!()
}

#[logic_rust]
#[trusted]
fn to_ty<T: Assoc>(x: T) -> T::Ty {
    panic!()
}

#[trusted]
#[ensures(a === from_ty(to_ty(a)))]
fn test<T: Assoc>(a: T) {}
