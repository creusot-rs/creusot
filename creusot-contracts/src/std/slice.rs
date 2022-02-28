use crate as creusot_contracts;
use creusot_contracts_proc::*;

extern_spec! {
  #[ensures((@s).len() === @result)]
  fn <[T]>::len<T>(s: &[T]) -> usize
}
