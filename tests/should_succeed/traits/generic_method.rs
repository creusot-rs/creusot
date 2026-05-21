use creusot_std::prelude::*;

pub trait Tr1 {
    type Ty;
}

pub trait Tr2 {
    #[logic]
    fn f<T: Tr1>(x: T::Ty) -> T::Ty;
}

pub struct S;

impl Tr2 for S {
    #[logic(opaque)]
    fn f<U: Tr1>(_x: U::Ty) -> U::Ty {
        dead
    }
}
