use crate as creusot_contracts;
use creusot_contracts_proc::*;

extern_spec! {
    #[requires(!(o === None))]
    #[ensures(Some(result) === o)]
    fn std::option::Option::unwrap<T>(o: Option<T>) -> T
}

extern_spec! {
    #[ensures(*o === None ==> result === None && ^o === None)]
    #[ensures(!(*o === None) ==>
              exists<r: &mut T> result === Some(r) && *o === Some(*r) && ^o === Some(^r))]
    fn std::option::Option::as_mut<T>(o: &mut Option<T>) -> Option<&mut T>
}

extern_spec! {
    #[ensures(*o === None ==> result === None)]
    #[ensures(!(*o === None) ==>
              exists<r: &mut T> result === Some(r) && *o === Some(*r))]
    fn std::option::Option::as_ref<T>(o: &Option<T>) -> Option<&T>
}
