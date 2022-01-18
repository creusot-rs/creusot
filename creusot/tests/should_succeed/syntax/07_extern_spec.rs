extern crate creusot_contracts;
use creusot_contracts::*;

extern_spec! {
    #[requires(true === true)]
    fn std::vec::Vec::new<T>() -> Vec<T>
}

extern_spec! {
    #[requires(spec1)]
    fn std::vec::Vec::from_elem<T : creusot::Clone>(e : T) -> Vec<T>
}

    #[requires(spec1)]
fn askdfjaskldjfklajdf_spec<T : creusot::Clone>(e : T) -> Vec<T> {
    std::vec::Vec::from_elem(e)
}




fn main() {
    let v: Vec<bool> = Vec::new();
}
