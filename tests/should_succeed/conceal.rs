use creusot_std::{logic::ops::*, prelude::*};

#[logic]
pub fn foo() -> Int {
    3
}

#[logic]
#[ensures(result == 4)]
pub fn bar<T>() -> Int {
    4
}

#[logic]
pub fn baz<T>() -> Int {
    5
}

pub trait Trait<'a> {
    type Assoc;

    #[logic]
    fn assoc() -> Int {
        0
    }
}

impl Trait<'_> for () {
    type Assoc = ();
}

impl<'a> Trait<'a> for &'a () {
    type Assoc = &'a ();
}

#[conceal(foo)]
#[conceal(bar::<&'static ()>)]
pub mod module {
    use super::*;

    #[logic]
    #[ensures(result == result)]
    #[reveal(foo)]
    pub fn no_bar_ref_unit<'a>() -> Int {
        foo() + bar::<<&'a () as Trait<'a>>::Assoc>() + bar::<u32>() + baz::<()>()
    }

    pub struct S<T>(T);

    #[reveal(bar::<&'static ()>)]
    mod module {
        use super::*;

        #[conceal(bar::<&T>)]
        impl<T> S<T> {
            #[logic]
            #[ensures(result == result)]
            fn no_foo_no_bar_ref_t() -> Int {
                foo() + bar::<T>() + bar::<&()>() + bar::<&T>()
            }

            #[logic]
            #[ensures(result == result)]
            #[reveal(bar::<&T>)]
            fn no_foo() -> Int {
                foo() + bar::<T>() + bar::<&()>() + bar::<&T>()
            }
        }

        #[conceal(bar::<&T>)]
        impl<T> Trait<'_> for &S<T> {
            type Assoc = T;

            #[logic]
            #[ensures(result == result)]
            fn assoc() -> Int {
                bar::<&T>()
            }
        }
    }
}

#[logic]
#[conceal(Int::div_logic)]
#[conceal(Int::rem_logic)]
#[ensures(result == x / 1)]
pub fn no_division(x: Int) -> Int {
    x / 1
}

#[conceal(recursive::cyclic)]
pub mod recursive {
    use super::*;

    #[logic]
    #[variant(x)]
    pub fn cyclic(x: Int) {
        if x > 0 {
            cyclic(x - 1);
        }
    }
}
