use creusot_contracts_proc::*;

use crate::Int;

#[creusot::builtins = "seq.Seq.seq"]
pub struct Seq<T>(std::marker::PhantomData<T>);

impl<T> Seq<T> {
    #[trusted]
    #[logic_rust]
    #[creusot::builtins = "seq.Seq.get"]
    pub fn index(self, _: Int) -> T {
        std::process::abort()
    }

    #[trusted]
    #[logic_rust]
    #[creusot::builtins = "seq.Seq.length"]
    pub fn len(self) -> Int {
        std::process::abort()
    }

    #[trusted]
    #[logic_rust]
    #[creusot::builtins = "seq.Seq.set"]
    pub fn set(self, _: Int, _: T) -> Self {
        std::process::abort()
    }

    #[trusted]
    #[logic_rust]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push(self, _: T) -> Self {
        std::process::abort()
    }
}
