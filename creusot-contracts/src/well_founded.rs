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
    #[logic]
    #[requires(forall<i: Int> i >= 0 ==> Self::well_founded_relation(s[i], s[i + 1]))]
    #[ensures(false)]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>);
}

/// This provides an easy way to prove the [`WellFounded`] condition, provided
/// that you can map your type to the integers.
#[logic]
#[requires(forall<t1: T, t2 : T> r[(t1, t2)] ==> Int::well_founded_relation(m[t1], m[t2]))]
#[ensures(!exists<s: Mapping<Int, T>>
    forall<i: Int> i >= 0 ==> r[(s[i], s[i + 1])]
)]
pub fn well_founded_map_to_nat<T>(r: Mapping<(T, T), bool>, m: Mapping<T, Int>) {
    pearlite! {
        if exists<s: Mapping<Int, T>> forall<i: Int> i >= 0 ==> r[(s[i], s[i + 1])] {
            let s = such_that(|s: Mapping<Int, T>| forall<i: Int> i >= 0 ==> r[(s[i], s[i + 1])]);
            Int::no_infinite_decreasing_sequence(|i: Int| m[s[i]]);
        }
    }
}

impl WellFounded for Int {
    #[logic]
    #[open]
    fn well_founded_relation(self, other: Self) -> bool {
        self >= 0 && self > other
    }

    #[trusted] // FIXME: find the right why3 lemma
    #[logic]
    #[requires(forall<i: Int> i >= 0 ==> Self::well_founded_relation(s[i], s[i + 1]))]
    #[ensures(false)]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) {}
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
            #[requires(forall<i: Int> i >= 0 ==> Self::well_founded_relation(s[i], s[i + 1]))]
            #[ensures(false)]
            fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) {
                pearlite! {
                    let map_to_nat = |x: Self| x@ + $t::MAX@ + 1;
                    well_founded_map_to_nat(|(x, y)| Self::well_founded_relation(x, y), map_to_nat);
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
    #[requires(forall<i: Int> i >= 0 ==> Self::well_founded_relation(s[i], s[i + 1]))]
    #[ensures(false)]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) {
        T::no_infinite_decreasing_sequence(|i| *s[i])
    }
}
