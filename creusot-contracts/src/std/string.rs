use crate::*;
use ::std::ops::Deref;

extern_spec! {
    mod std {
        mod string {
            impl Deref for String {
                #[pure]
                #[ensures(result@ == self@)]
                fn deref(&self) -> &str;
            }

            impl String {
                #[pure]
                #[ensures(result@ == self@.len())]
                fn len(&self) -> usize;
            }
        }
    }
}

extern_spec! {
    impl str {
        #[terminates] // can OOM (?)
        #[ensures(result@ == self@)]
        fn to_string(&self) -> String;

        #[pure]
        #[requires(ix@ < self@.len())]
        #[ensures(result.0@.concat(result.1@) == self@)]
        #[ensures(result.0@.len() == ix@)]
        fn split_at(&self, ix : usize) -> (&str, &str);
    }
}
