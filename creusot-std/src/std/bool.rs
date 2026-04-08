use crate::prelude::*;

extern_spec! {
    impl bool {
        #[check(ghost)]
        #[ensures(result == if self { Some(t) } else { None })]
        fn then_some<T>(self, t: T) -> Option<T> {
            if self { Some(t) } else { None }
        }

        #[requires(|mode| self ==> f.precondition(mode, ()))]
        #[ensures(|result| !self ==> result == None)]
        #[ensures(|result, mode| self ==>
            match result {
                None => false,
                Some(t) => f.postcondition_once(mode, (), t)
            }
        )]
        fn then<T, F: FnOnce() -> T>(self, f: F) -> Option<T> {
            if self { Some(f()) } else { None }
        }
    }
}
