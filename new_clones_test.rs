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
//
//
use ::std::cmp::Ordering;
pub trait OrdLogic {
    #[logic]
    fn cmp_log(self, _: Self) -> Ordering;

    #[predicate]
    fn le_log(self, o: Self) -> bool {
        pearlite! { self.cmp_log(o) != Ordering::Greater }
    }

    #[law]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    fn cmp_le_log(x: Self, y: Self);

    // #[predicate]
    // fn lt_log(self, o: Self) -> bool {
    //     pearlite! { self.cmp_log(o) == Ordering::Less }
    // }

    // #[law]
    // #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    // fn cmp_lt_log(x: Self, y: Self);

    // #[predicate]
    // fn ge_log(self, o: Self) -> bool {
    //     pearlite! { self.cmp_log(o) != Ordering::Less }
    // }

    // #[law]
    // #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    // fn cmp_ge_log(x: Self, y: Self);

    // #[predicate]
    // fn gt_log(self, o: Self) -> bool {
    //     pearlite! { self.cmp_log(o) == Ordering::Greater }
    // }

    // #[law]
    // #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    // fn cmp_gt_log(x: Self, y: Self);

    // #[law]
    // #[ensures(x.cmp_log(x) == Ordering::Equal)]
    // fn refl(x: Self);

    // #[law]
    // #[requires(x.cmp_log(y) == o)]
    // #[requires(y.cmp_log(z) == o)]
    // #[ensures(x.cmp_log(z) == o)]
    // fn trans(x: Self, y: Self, z: Self, o: Ordering);

    // #[law]
    // #[requires(x.cmp_log(y) == Ordering::Less)]
    // #[ensures(y.cmp_log(x) == Ordering::Greater)]
    // fn antisym1(x: Self, y: Self);

    // #[law]
    // #[requires(x.cmp_log(y) == Ordering::Greater)]
    // #[ensures(y.cmp_log(x) == Ordering::Less)]
    // fn antisym2(x: Self, y: Self);

    // #[law]
    // #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    // fn eq_cmp(x: Self, y: Self);
}

impl<A: OrdLogic, B: OrdLogic> OrdLogic for (A, B) {
    #[logic]
    fn cmp_log(self, o: Self) -> Ordering {
        pearlite! { {
            let r = self.0.cmp_log(o.0);
            if r == Ordering::Equal {
                self.1.cmp_log(o.1)
            } else {
                r
            }
        } }
    }

    // #[predicate]
    // fn le_log(self, o: Self) -> bool {
    //     pearlite! { (self.0 == o.0 && self.1 <= o.1) || self.0 <= o.0 }
    // }

    #[logic]
    fn cmp_le_log(_: Self, _: Self) {}

    // #[predicate]
    // fn lt_log(self, o: Self) -> bool {
    //     pearlite! { (self.0 == o.0 && self.1 < o.1) || self.0 < o.0 }
    // }

    // #[logic]
    // fn cmp_lt_log(_: Self, _: Self) {}

    // #[predicate]
    // fn ge_log(self, o: Self) -> bool {
    //     pearlite! { (self.0 == o.0 && self.1 >= o.1) || self.0 >= o.0 }
    // }

    // #[logic]
    // fn cmp_ge_log(_: Self, _: Self) {}

    // #[predicate]
    // fn gt_log(self, o: Self) -> bool {
    //     pearlite! { (self.0 == o.0 && self.1 > o.1) || self.0 > o.0 }
    // }

    // #[logic]
    // fn cmp_gt_log(_: Self, _: Self) {}

    // #[logic]
    // fn refl(_: Self) {}

    // #[logic]
    // fn trans(_: Self, _: Self, _: Self, _: Ordering) {}

    // #[logic]
    // fn antisym1(_: Self, _: Self) {}

    // #[logic]
    // fn antisym2(_: Self, _: Self) {}

    // #[logic]
    // fn eq_cmp(_: Self, _: Self) {}
}
