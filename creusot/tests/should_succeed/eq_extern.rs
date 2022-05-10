extern crate creusot_contracts;
use creusot_contracts::*;

extern_spec! {
    #[ensures(result === (@self_).cmp_log(@*o))]
    fn std::cmp::Ord::cmp<Self_>(self_: &Self_, o: &Self_) -> Ordering
        where Self_: Ord,
              Self_: Model,
              Self_::ModelTy: OrdLogic
}

fn use_ord<K: Ord>(t: &K, u: &K)
where
    K: Model,
    K::ModelTy: OrdLogic,
{
    t.cmp(u);
}
