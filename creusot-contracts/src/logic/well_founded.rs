#[cfg(creusot)]
use crate::logic::{Mapping, such_that, unreachable};
use crate::prelude::*;

/// Instances of this trait are types which are allowed as variants of recursive definitions.
pub trait WellFounded: Sized {
    /// Relation used to specify well-foundedness.
    #[logic]
    #[intrinsic("well_founded_relation")]
    fn well_founded_relation(self, other: Self) -> bool;

    /// Being well-founded means that there is no infinitely decreasing sequence.
    ///
    /// If you can map your type to another that already implements `WellFounded`
    /// (and the mapping preserves `well_founded_relation`), this lemma is quite
    /// easy to prove:
    ///
    /// ```
    /// # use creusot_contracts::{prelude::*, well_founded::WellFounded};
    /// struct MyInt(Int);
    /// impl WellFounded for MyInt {
    ///     #[logic(open, inline)]
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
    #[logic(open, inline)]
    fn well_founded_relation(self, other: Self) -> bool {
        self >= 0 && self > other
    }

    #[trusted]
    #[logic(opaque)]
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
            #[logic(open, inline)]
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
    #[logic(open, inline)]
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
    #[logic(open, inline)]
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

// === Implementation of `WellFounded` for tuples up to size 8.

impl WellFounded for () {
    #[logic(open, inline)]
    fn well_founded_relation(self, _: Self) -> bool {
        false
    }

    #[logic]
    #[ensures(result >= 0)]
    #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int {
        0
    }
}

macro_rules! impl_tuple_to_pair {
    ( $t1:ident = $idx1:tt, $($ts:ident = $idxs:tt,)* ) => {
        #[cfg(creusot)]
        #[allow(unused_parens)]
        impl<$t1, $($ts),*> TupleToPair for ($t1, $($ts,)*) {
            type Target = ($t1, ($($ts,)*));
            #[logic]
            fn tuple_to_pair(self) -> Self::Target {
                (self.0, ($( self . $idxs, )*))
            }
        }
    };
}

/// Convert a tuple to a pair, because the lemmas below act on pairs.
#[cfg(creusot)]
trait TupleToPair {
    type Target;
    #[logic]
    fn tuple_to_pair(self) -> Self::Target;
}

macro_rules! wf_tuples {
    () => {};
    ( $($ts:ident = $idxs:tt),+ ) => {
        impl_tuple_to_pair!($($ts=$idxs,)+);
        wf_tuples!( @impl $($ts=$idxs),+ );
        wf_tuples!( @pop_last [$($ts=$idxs),+] [] );
    };
    // its a bit hard to remove the _last_ element of a sequence in macros: we need this little helper.
    (@pop_last [$t:ident=$idx:tt , $($ts:ident=$idxs:tt),+] [$($ts2:ident=$idxs2:tt),*]) => {
        wf_tuples!( @pop_last [$($ts=$idxs),+] [$($ts2=$idxs2,)* $t=$idx] );
    };
    (@pop_last [$t:ident=$idx:tt]                           [$($ts2:ident=$idxs2:tt),*]) => {
        wf_tuples!( $($ts2 = $idxs2),* );
    };
    ( @impl $($ts:ident = $idxs:tt),+ ) => {
        impl<$($ts),+> WellFounded for ($($ts,)+)
        where $($ts : WellFounded),+
        {
            wf_tuples!( @wf_relation self other {} [] $($ts=$idxs)+ );

            #[logic]
            #[ensures(result >= 0)]
            #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
            fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int {
                pearlite! {
                    if exists<r> r >= 0 && !Self::well_founded_relation(s[r], s[r + 1]) {
                        such_that(|r| r >= 0 && !Self::well_founded_relation(s[r], s[r + 1]))
                    } else {
                        let _ = T0::no_infinite_decreasing_sequence(first_component_decr(|i| s[i].tuple_to_pair()));
                        unreachable()
                    }
                }
            }
        }
    };
    ( @wf_relation $name1:ident $name2:ident {$($res:expr)?} [$($to_eq:tt)*] $t:ident = $idx:tt $($ts:ident = $idxs:tt)* ) => {
        wf_tuples!{ @wf_relation $name1 $name2
            {$($res ||)? ($(($name1 . $to_eq == $name2 . $to_eq ) &&)* $t::well_founded_relation($name1 . $idx, $name2 . $idx))}
            [$($to_eq)* $idx]
            $($ts=$idxs)*
        }
    };
    ( @wf_relation $name1:ident $name2:ident {$res:expr} [$($to_eq:tt)*] ) => {
        #[logic(open, inline)]
        fn well_founded_relation($name1, $name2: Self) -> bool {
            $res
        }
    };
}

wf_tuples!(T0 = 0, T1 = 1, T2 = 2, T3 = 3, T4 = 4, T5 = 5, T6 = 6, T7 = 7);

/// Get an index > i, such that `s[index] < s[i]`.
#[logic]
#[requires(forall<i> 0 <= i ==> <(T1, T2)>::well_founded_relation(s[i], s[i + 1]))]
#[requires(0 <= i)]
#[ensures(i < result)]
#[ensures(T1::well_founded_relation(s[i].0, s[result].0))]
#[variant(s[i].1)]
fn extract_next_decr<T1: WellFounded, T2: WellFounded>(s: Mapping<Int, (T1, T2)>, i: Int) -> Int {
    if T1::well_founded_relation(s[i].0, s[i + 1].0) { i + 1 } else { extract_next_decr(s, i + 1) }
}

/// Used to construct [`first_component_decr`] below.
#[logic]
#[requires(forall<i> 0 <= i ==> <(T1, T2)>::well_founded_relation(s[i], s[i + 1]))]
#[requires(0 <= i)]
#[ensures(0 <= result)]
#[ensures(0 < i ==> {
    let prev = extract_nth(s, i - 1);
    prev < result &&
    T1::well_founded_relation(s[prev].0, s[result].0)
})]
#[variant(i)]
fn extract_nth<T1: WellFounded, T2: WellFounded>(s: Mapping<Int, (T1, T2)>, i: Int) -> Int {
    if i == 0 {
        0
    } else {
        let prev = extract_nth(s, i - 1);
        extract_next_decr(s, prev)
    }
}

/// Prove that `s` being infinitely decreasing is contradictory, by extracting
/// a sequence such that the first component decreases.
#[logic]
#[requires(forall<i> 0 <= i ==> <(T1, T2)>::well_founded_relation(s[i], s[i + 1]))]
#[ensures(forall<i> 0 <= i ==> T1::well_founded_relation(result[i], result[i + 1]))]
fn first_component_decr<T1: WellFounded, T2: WellFounded>(
    s: Mapping<Int, (T1, T2)>,
) -> Mapping<Int, T1> {
    |i| if 0 <= i { s[extract_nth(s, i)].0 } else { such_that(|_| true) }
}
