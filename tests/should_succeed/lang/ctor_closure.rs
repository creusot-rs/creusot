extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == o.map_logic(|x| Some(x)))]
pub fn g<A>(o: Option<A>) -> Option<Option<A>> {
    o.map(Some)
}

pub struct T0();

pub fn h() -> T0 {
    let t = T0;
    t()
}

#[allow(dead_code)]
pub struct T2<A, B>(A, B);

impl<A, B> Invariant for T2<A, B> {
    #[logic(opaque)]
    fn invariant(self) -> bool {
        dead
    }
}

#[requires(inv(T2(x, y)))]
#[ensures(result == T2(x, y))]
pub fn i<A, B>(x: A, y: B) -> T2<A, B> {
    let t = T2;
    t(x, y)
}

#[logic]
#[ensures(T2.precondition((x, x)) == inv(T2(x, x)))]
pub fn some_post<A>(x: A) {}
