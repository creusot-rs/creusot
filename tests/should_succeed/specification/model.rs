extern crate creusot_contracts;
use creusot_contracts::{logic::Int, *};

pub struct Seven();

impl View for Seven {
    type ViewTy = Int;

    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[trusted]
#[ensures(result@ == 7)]
pub fn seven() -> Seven {
    Seven()
}

pub struct Pair<T, U>(T, U);

impl<T, U> View for Pair<T, U> {
    type ViewTy = (T, U);

    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[trusted]
#[ensures(result@ == (a, b))]
pub fn pair<T, U>(a: T, b: U) -> Pair<T, U> {
    Pair(a, b)
}

#[requires(a@@ == 0)]
pub fn test_arc(a: std::sync::Arc<usize>) {}

#[requires(v@@ == 0)]
pub fn test_rc(v: std::rc::Rc<usize>) {}
