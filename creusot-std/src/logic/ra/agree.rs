use crate::{logic::ra::RA, prelude::*};

/// The 'agreement' Resource Algebra.
///
/// This has the property that all resource with the same id have the same value
/// (they 'agree').
pub struct Ag<T>(pub T);

impl<T> RA for Ag<T> {
    #[logic(open)]
    fn op(self, other: Self) -> Option<Self> {
        if self.0 == other.0 { Some(self) } else { None }
    }

    #[logic(open)]
    fn incl(self, other: Self) -> bool {
        self.0 == other.0
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[allow(unused_variables)]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open)]
    fn core(self) -> Option<Self> {
        Some(self)
    }

    #[logic]
    #[ensures({
        let c = self.core().unwrap_logic();
        c.op(c) == Some(c)
    })]
    #[ensures(self.core().unwrap_logic().op(self) == Some(self))]
    fn core_idemp(self) {}

    #[logic]
    #[allow(unused_variables)]
    fn core_is_maximal_idemp(self, i: Self) {}

    #[logic(open)]
    fn cancelable(self) -> bool {
        true
    }
}
