extern crate creusot_contracts;
use creusot_contracts::*;

// extern_spec! {
//     #[ensures(@self_ === @rhs)]
//     fn std::cmp::PartialEq::eq<T, Rhs>(self_: &T, rhs: &Rhs) -> bool
//         where T : PartialEq<Rhs>,
//               T : Model,
//               Rhs: Model<ModelTy = T::ModelTy>,
// }

// fn use_eq<U, T: PartialEq<U>>(a: T, b: U)
// where
//     U: Model,
//     T: Model<ModelTy = U::ModelTy>,
// {
//     a == b;
// }

extern_spec! {
    #[ensures(result === (@self_).cmp_log(@*o))]
    fn std::cmp::Ord::cmp<T>(self_: &T, o: &T) -> Ordering
        where T: Ord,
              T: Model,
              T::ModelTy: OrdLogic
}

fn use_ord<K: Ord>(t: &K, u: &K)
where
    K: Model,
    K::ModelTy: OrdLogic,
{
    t.cmp(u);
}
