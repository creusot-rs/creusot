use crate::{logic::ra::RA, *};

/// The 'agreement' Resource Algebra.
///
/// This has the property that all resource with the same id have the same value
/// (they 'agree').
pub struct Ag<T>(pub T);

impl<T> RA for Ag<T> {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        if self.0 == other.0 { Some(self) } else { None }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        self.op(factor)
    }

    #[logic(law)]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[logic(law)]
    #[open(self)]
    #[ensures(a.op(b).and_then_logic(|ab : Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => c.op(c) == Some(c) && c.op(self) == Some(self),
        None => true
    })]
    fn core(self) -> Option<Self> {
        Some(self)
    }

    #[logic]
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self) {}
}
