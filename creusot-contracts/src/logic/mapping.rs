use creusot_contracts_proc::*;

use crate::logic::*;

#[creusot::builtins = "map.Map.map"]
pub struct Mapping<A, B>(std::marker::PhantomData<(A, B)>);

impl<A, B> Mapping<A, B> {
    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Map.get"]
    pub fn get(self, _: A) -> B {
        std::process::abort()
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Map.set"]
    pub fn set(self, _: A, _: B) -> Self {
        std::process::abort()
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "map.Const.const"]
    pub fn cst(_: B) -> Self {
        std::process::abort()
    }
}

impl<A, B> EqLogic for Mapping<A, B> {
    #[trusted]
    #[logic]
    #[creusot::builtins = "map.MapExt.(==)"]
    fn log_eq(self, _: Self) -> bool {
        std::process::abort()
    }

    #[predicate]
    fn log_ne(self, o: Self) -> bool {
        std::process::abort()
    }

    #[logic]
    fn eq_ne(_: Self, _: Self) {
        std::process::abort()
    }

    #[logic]
    fn refl(_: Self) {
        ()
    }

    #[logic]
    fn symmetry(_: Self, _: Self) {
        ()
    }

    #[logic]
    fn transitivity(_: Self, _: Self, _: Self) {
        ()
    }
}
