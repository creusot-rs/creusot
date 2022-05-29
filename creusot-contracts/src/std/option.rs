use crate as creusot_contracts;
use crate::std::default::DefaultSpec;
use creusot_contracts_proc::*;

extern_spec! {
    mod std {
        mod option {
            impl<T> Option<T> {
                #[requires(self != None)]
                #[ensures(Some(result) == self)]
                fn unwrap(self) -> T;

                #[ensures(*self == None ==> result == None && ^self == None)]
                #[ensures(*self == None || exists<r: &mut T> result == Some(r) && *self == Some(*r) && ^self == Some(^r))]
                fn as_mut(&mut self) -> Option<&mut T>;

                #[ensures(*self == None ==> result == None)]
                #[ensures(*self == None || exists<r: &mut T> result == Some(r) && *self == Some(*r))]
                fn as_ref(&self) -> Option<&T>;
            }
        }
    }
}

impl<T> DefaultSpec for Option<T> {
    #[logic]
    fn default_log() -> Option<T> {
        None
    }
}
