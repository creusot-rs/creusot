#![feature(register_tool, rustc_attrs)]
#![register_tool(creusot)]
#![feature(proc_macro_hygiene, stmt_expr_attributes)]

extern crate creusot_contracts;

use creusot_contracts::*;

pub trait Model {
    type ModelTy;

    fn model(self) -> Self::ModelTy;
}

impl<T: Model> Model for &T {
    type ModelTy = T::ModelTy;

    fn model(self) -> Self::ModelTy {
        self.model()
    }
}