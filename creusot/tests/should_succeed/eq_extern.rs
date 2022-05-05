extern crate creusot_contracts;
use creusot_contracts::*;

extern_spec! {
    #[ensures(@self_ === @rhs)]
    fn std::cmp::PartialEq::eq<T, Rhs>(self_: &T, rhs: &Rhs) -> bool
        where T : PartialEq<Rhs>,
              T : Model,
              Rhs: Model<ModelTy = T::ModelTy>,
}

fn use_eq<U, T: PartialEq<U>>(a: T, b: U)
where
    U: Model,
    T: Model<ModelTy = U::ModelTy>,
{
    a == b;
}
