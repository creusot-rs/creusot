#[cfg(creusot)]
use crate::logic::such_that;
use crate::{
    logic::ra::{
        RA,
        update::{LocalUpdate, Update},
    },
    prelude::*,
};

/// The 'sum' (or 'either') Resource Algebra.
///
/// This represents a resource that is in two possible states. Combining a `Left` with
/// a `Right` is invalid.
pub enum Sum<T, U> {
    Left(T),
    Right(U),
}

impl<R1: RA, R2: RA> RA for Sum<R1, R2> {
    #[logic(open)]
    fn op(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Left(x), Self::Left(y)) => x.op(y).map_logic(|l| Self::Left(l)),
            (Self::Right(x), Self::Right(y)) => x.op(y).map_logic(|r| Self::Right(r)),
            _ => None,
        }
    }

    #[logic(open)]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        match (self, factor) {
            (Self::Left(x), Self::Left(y)) => x.factor(y).map_logic(|l| Self::Left(l)),
            (Self::Right(x), Self::Right(y)) => x.factor(y).map_logic(|r| Self::Right(r)),
            _ => None,
        }
    }

    #[logic(open(self), law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[logic(open(self), law)]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open)]
    fn core(self) -> Option<Self> {
        match self {
            Self::Left(x) => x.core().map_logic(|l| Self::Left(l)),
            Self::Right(x) => x.core().map_logic(|r| Self::Right(r)),
        }
    }

    #[logic]
    #[requires(self.core() != None)]
    #[ensures({
        let c = self.core().unwrap_logic();
        c.op(c) == Some(c)
    })]
    #[ensures(self.core().unwrap_logic().op(self) == Some(self))]
    fn core_idemp(self) {
        let _ = R1::core_idemp;
        let _ = R2::core_idemp;
    }

    #[logic]
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self) {
        match (self, i) {
            (Sum::Left(s), Sum::Left(i)) => s.core_is_maximal_idemp(i),
            (Sum::Right(s), Sum::Right(i)) => s.core_is_maximal_idemp(i),
            _ => (),
        }
    }
}

pub struct SumUpdateL<U>(pub U);

impl<R1: RA, R2: RA, U: Update<R1>> Update<Sum<R1, R2>> for SumUpdateL<U> {
    type Choice = U::Choice;

    #[logic(open)]
    fn premise(self, from: Sum<R1, R2>) -> bool {
        match from {
            Sum::Left(from) => self.0.premise(from),
            Sum::Right(_) => false,
        }
    }

    #[logic(open)]
    #[requires(self.premise(from))]
    fn update(self, from: Sum<R1, R2>, ch: U::Choice) -> Sum<R1, R2> {
        match from {
            Sum::Left(from) => Sum::Left(self.0.update(from, ch)),
            x => x, /* Dummy */
        }
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: Sum<R1, R2>, frame: Sum<R1, R2>) -> U::Choice {
        match (from, frame) {
            (Sum::Left(from), Sum::Left(frame)) => self.0.frame_preserving(from, frame),
            _ => such_that(|_| true),
        }
    }
}

pub struct SumUpdateR<U>(pub U);

impl<R: RA, U: Update<R>, V: RA> Update<Sum<V, R>> for SumUpdateR<U> {
    type Choice = U::Choice;

    #[logic(open)]
    fn premise(self, from: Sum<V, R>) -> bool {
        match from {
            Sum::Right(from) => self.0.premise(from),
            Sum::Left(_) => false,
        }
    }

    #[logic(open)]
    #[requires(self.premise(from))]
    fn update(self, from: Sum<V, R>, ch: U::Choice) -> Sum<V, R> {
        match from {
            Sum::Right(from) => Sum::Right(self.0.update(from, ch)),
            x => x, /* Dummy */
        }
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: Sum<V, R>, frame: Sum<V, R>) -> U::Choice {
        match (from, frame) {
            (Sum::Right(from), Sum::Right(frame)) => self.0.frame_preserving(from, frame),
            _ => such_that(|_| true),
        }
    }
}

pub struct SumLocalUpdateL<U>(pub U);

impl<R1: RA, R2: RA, U: LocalUpdate<R1>> LocalUpdate<Sum<R1, R2>> for SumLocalUpdateL<U> {
    #[logic(open)]
    fn premise(self, from_auth: Sum<R1, R2>, from_frag: Sum<R1, R2>) -> bool {
        match (from_auth, from_frag) {
            (Sum::Left(from_auth), Sum::Left(from_frag)) => self.0.premise(from_auth, from_frag),
            (Sum::Right(_), Sum::Right(_)) => false,
            _ => true,
        }
    }

    #[logic(open)]
    fn update(self, from_auth: Sum<R1, R2>, from_frag: Sum<R1, R2>) -> (Sum<R1, R2>, Sum<R1, R2>) {
        match (from_auth, from_frag) {
            (Sum::Left(from_auth), Sum::Left(from_frag)) => {
                let (to_auth, to_frag) = self.0.update(from_auth, from_frag);
                (Sum::Left(to_auth), Sum::Left(to_frag))
            }
            _ => such_that(|_| true),
        }
    }

    #[logic]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(
        self,
        from_auth: Sum<R1, R2>,
        from_frag: Sum<R1, R2>,
        frame: Option<Sum<R1, R2>>,
    ) {
        match (from_auth, from_frag, frame) {
            (Sum::Left(from_auth), Sum::Left(from_frag), Some(Sum::Left(frame))) => {
                self.0.frame_preserving(from_auth, from_frag, Some(frame))
            }
            (Sum::Left(from_auth), Sum::Left(from_frag), None) => {
                self.0.frame_preserving(from_auth, from_frag, None)
            }
            _ => (),
        }
    }
}

pub struct SumLocalUpdateR<U>(pub U);

impl<R1: RA, R2: RA, U: LocalUpdate<R2>> LocalUpdate<Sum<R1, R2>> for SumLocalUpdateR<U> {
    #[logic(open)]
    fn premise(self, from_auth: Sum<R1, R2>, from_frag: Sum<R1, R2>) -> bool {
        match (from_auth, from_frag) {
            (Sum::Right(from_auth), Sum::Right(from_frag)) => self.0.premise(from_auth, from_frag),
            (Sum::Left(_), Sum::Left(_)) => false,
            _ => true,
        }
    }

    #[logic(open)]
    fn update(self, from_auth: Sum<R1, R2>, from_frag: Sum<R1, R2>) -> (Sum<R1, R2>, Sum<R1, R2>) {
        match (from_auth, from_frag) {
            (Sum::Right(from_auth), Sum::Right(from_frag)) => {
                let (to_auth, to_frag) = self.0.update(from_auth, from_frag);
                (Sum::Right(to_auth), Sum::Right(to_frag))
            }
            _ => such_that(|_| true),
        }
    }

    #[logic]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(
        self,
        from_auth: Sum<R1, R2>,
        from_frag: Sum<R1, R2>,
        frame: Option<Sum<R1, R2>>,
    ) {
        match (from_auth, from_frag, frame) {
            (Sum::Right(from_auth), Sum::Right(from_frag), Some(Sum::Right(frame))) => {
                self.0.frame_preserving(from_auth, from_frag, Some(frame))
            }
            (Sum::Right(from_auth), Sum::Right(from_frag), None) => {
                self.0.frame_preserving(from_auth, from_frag, None)
            }
            _ => (),
        }
    }
}
