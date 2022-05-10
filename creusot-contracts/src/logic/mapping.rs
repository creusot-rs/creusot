use crate as creusot_contracts;
use creusot_contracts_proc::*;

#[creusot::builtins = "map.Map.map"]
pub struct Mapping<A, B>(std::marker::PhantomData<(A, B)>);

impl<A, B> Mapping<A, B> {
    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Map.get"]
    pub fn get(self, _: A) -> B {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Map.set"]
    pub fn set(self, _: A, _: B) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Const.const"]
    pub fn cst(_: B) -> Self {
        absurd
    }
}
