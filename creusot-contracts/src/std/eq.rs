use crate as creusot_contracts;
use creusot_contracts_proc::*;

use crate::logic::*;

extern_spec! {
    #[ensures(result === (@self_ === @rhs))]
    fn std::cmp::PartialEq::eq<Self_, Rhs>(self_: &Self_, rhs: &Rhs) -> bool
        where Self_ : PartialEq<Rhs>,
              Self_ : Model,
              Rhs: Model<ModelTy = Self_::ModelTy>,
}
