// UISKIP WHY3SKIP
use creusot_contracts::{
    logic::{Mapping, WellFounded},
    *,
};

/// Variant that decreases both components.
pub struct CustomVariant(pub u32, pub u32);

impl WellFounded for CustomVariant {
    #[logic(open)]
    fn well_founded_relation(self, other: Self) -> bool {
        self.0 > other.0 && self.1 > other.1
    }

    #[logic]
    #[ensures(result >= 0)]
    #[ensures(!Self::well_founded_relation(s[result], s[result + 1]))]
    fn no_infinite_decreasing_sequence(s: Mapping<Int, Self>) -> Int {
        // An infinite decreasing sequence means, in particular, that the first
        // component of CustomVariant is infinitely decreasing.
        u32::no_infinite_decreasing_sequence(|i: Int| s[i].0)
    }
}
