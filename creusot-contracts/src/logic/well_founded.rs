#[cfg(creusot)]
use crate::logic::Mapping;
use crate::*;

/// Instances of this trait are types which are allowed as variants of recursive definitions.
pub trait WellFounded: Sized {
    /// Relation used to specify well-foundedness.
    #[logic]
    #[rustc_diagnostic_item = "creusot_wf_relation"]
    fn well_founded_relation(self, other: Self) -> bool;

    /// Being well-founded means that there is no infinitely decreasing sequence.
    ///
    /// If you can map your type to another that already implements `WellFounded`
    /// (and the mapping preserves `well_founded_relation`), this lemma is quite
    /// easy to prove:
    ///
    /// ```
    /// # use creusot_contracts::{*, well_founded::WellFounded};
    /// struct MyInt(Int);
    /// impl WellFounded for MyInt {
    ///     #[logic]
    ///     #[open]
    ///     fn well_founded_relation(self, other: Self) -> bool {
    ///         Int::well_founded_relation(self.0, other.0)
    ///     }
    ///
    ///     #[logic]
    ///     #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
    ///     fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int {
    ///         Int::no_infinite_decreasing_sequence(|i| s[i].0)
    ///     }
    /// }
    /// ```
    #[logic]
    #[ensures(result >= 0)]
    #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int;
}

impl WellFounded for Int {
    #[logic]
    #[open]
    fn well_founded_relation(self, other: Self) -> bool {
        self >= 0 && self > other
    }

    #[trusted]
    #[logic]
    #[ensures(result >= 0)]
    #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int {
        dead
    }
}

macro_rules! impl_well_founded {
    ($($t:ty),*) => {
        $(

        impl WellFounded for $t {
            #[logic]
            #[open]
            fn well_founded_relation(self, other: Self) -> bool {
                self > other
            }

            #[logic]
            #[ensures(result >= 0)]
            #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
            fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int {
                pearlite! {
                    Int::no_infinite_decreasing_sequence(|i| s[i]@ - $t::MIN@)
                }
            }
        }

        )*
    };
}

impl_well_founded!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<T: WellFounded> WellFounded for &T {
    #[logic]
    #[open]
    fn well_founded_relation(self, other: Self) -> bool {
        T::well_founded_relation(*self, *other)
    }

    #[logic]
    #[ensures(result >= 0)]
    #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int {
        T::no_infinite_decreasing_sequence(|i| *s[i])
    }
}

impl<T: WellFounded> WellFounded for Box<T> {
    #[logic]
    #[open]
    fn well_founded_relation(self, other: Self) -> bool {
        T::well_founded_relation(*self, *other)
    }

    #[logic]
    #[ensures(result >= 0)]
    #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int {
        T::no_infinite_decreasing_sequence(|i| *s[i])
    }
}
