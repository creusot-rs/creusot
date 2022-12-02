extern crate creusot_contracts;

use creusot_contracts::*;

// #[predicate]
// fn omg() -> bool {
//     true
// }

// #[predicate]
// fn call_function() -> bool {
//     omg()
// }

pub trait DeepModel {
    type DeepModelTy;
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy;
}

impl<T: DeepModel + ?Sized> DeepModel for &T {
    type DeepModelTy = T::DeepModelTy;
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        (*self).deep_model()
    }
}

// fn omgomg() {
//     1 + 1;
// }

// struct Test {}

// fn omg_2() {
//     Test {};
// }

// enum Option<T> {
//     Some(T),
//     None,
// }
// use Option::*;

// fn inexhaustive_match(x: Option<()>) {
//     match x {
//         None => (),
//         Some(_) => (),
//     }
// }

// trait BinOp {
//     #[logic]
//     fn op(self, _: Self) -> Self;

//     #[logic]
//     #[ensures(self.op(b) == b.op(self))]
//     fn symm(self, b: Self);
// }

// impl BinOp for () {
//     #[logic]
//     fn op(self, _: Self) -> Self {
//         ()
//     }

//     #[logic]
//     #[ensures(self.op(b) == b.op(self))]
//     fn symm(self, b: Self) {}
// }
