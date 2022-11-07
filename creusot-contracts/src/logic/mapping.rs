use crate::*;
use crate::prusti_prelude::logic as prusti_logic;

#[cfg_attr(feature = "contracts", creusot::builtins = "map.Map.map")]
pub struct Mapping<A, B>(std::marker::PhantomData<(A, B)>);

impl<A, B> Mapping<A, B> {
    #[trusted]
    #[prusti_logic(('x, '_) -> 'x)]
    #[creusot::builtins = "map.Map.get"]
    pub fn get(self, _: A) -> B {
        absurd
    }

    #[trusted]
    #[prusti_logic(('x, '_, 'x) -> 'x)]
    #[creusot::builtins = "map.Map.set"]
    pub fn set(self, _: A, _: B) -> Self {
        absurd
    }

    #[trusted]
    #[prusti_logic(('x) -> 'x)]
    #[creusot::builtins = "map.Const.const"]
    pub fn cst(_: B) -> Self {
        absurd
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "prelude.Mapping.from_fn"]
    pub fn from_fn<F: FnOnce(A) -> B>(_: F) -> Self {
        absurd
    }
}
