use crate::*;
mod arithmetic;

pub use self::arithmetic::{
    AddLogic, DivLogic, MulLogic, NegLogic, NthBitLogic, RemLogic, SubLogic,
};

/// Used for indexing operations (`container[index]`) in pearlite.
#[diagnostic::on_unimplemented(
    message = "the type `{Self}` cannot be indexed by `{I}` in logic",
    label = "`{Self}` cannot be indexed by `{I}` in logic"
)]
pub trait IndexLogic<I: ?Sized> {
    type Item;

    /// Performs the indexing (`container[index]`) operation.
    #[logic]
    #[rustc_diagnostic_item = "creusot_index_logic_method"]
    fn index_logic(self, idx: I) -> Self::Item;
}
