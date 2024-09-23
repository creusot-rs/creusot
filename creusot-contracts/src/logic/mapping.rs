use crate::*;

#[trusted]
#[cfg_attr(creusot, creusot::builtins = "map.Map.map")]
pub struct Mapping<A: ?Sized, B: ?Sized>(std::marker::PhantomData<A>, std::marker::PhantomData<B>);

impl<A: ?Sized, B: ?Sized> Mapping<A, B> {
    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "map.Map.get"]
    pub fn get(self, _: A) -> B
    where
        B: Sized, // TODO : don't require this (problem: return type needs to be sized)
    {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "map.Map.set"]
    pub fn set(self, _: A, _: B) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[open(self)]
    #[creusot::builtins = "map.Const.const"]
    pub fn cst(_: B) -> Self {
        absurd
    }
}
