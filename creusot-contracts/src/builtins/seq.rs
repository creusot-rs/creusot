use creusot_contracts_proc::*;

use crate::Int;

#[creusot::builtins = "seq.Seq.seq"]
pub struct Seq<T>(std::marker::PhantomData<T>);

impl<T> Seq<T> {
    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.get"]
    pub fn index(self, _: Int) -> T {
        std::process::abort()
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.length"]
    pub fn len(self) -> Int {
        std::process::abort()
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.set"]
    pub fn set(self, _: Int, _: T) -> Self {
        std::process::abort()
    }

    #[trusted]
    #[logic]
    #[creusot::builtins = "seq.Seq.snoc"]
    pub fn push(self, _: T) -> Self {
        std::process::abort()
    }
    #[predicate]
    pub fn permutation_of(self, o: Self) -> bool {
        self.permut(o, 0, self.len())
    }

    #[trusted]
    #[predicate]
    #[creusot::builtins = "seq.Permut.permut"]
    pub fn permut(self, _: Self, _: Int, _: Int) -> bool {
        std::process::abort()
    }
}
