use crate::*;

#[cfg_attr(creusot, creusot::builtins = "map.Map.map")]
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

    #[cfg_attr(creusot, creusot::no_translate)]
    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.Mapping.from_fn"]
    pub fn from_fn<F: FnOnce(A) -> B>(_: F) -> Self {
        absurd
    }
}
