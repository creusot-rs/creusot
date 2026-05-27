use crate::{
    logic::ra::{
        RA, UnitRA,
        update::{LocalUpdate, Update},
    },
    prelude::*,
};

// TODO: general tuples

macro_rules! ra_tuples {
    ($(($t:ident, $n:tt, $v:ident))*) => {

impl<$($t : RA),*> RA for ($($t),*) {
    #[logic(open)]
    fn op(self, other: Self) -> Option<Self> {
        match ($(self.$n.op(other.$n)),*) {
            ($(Some($v)),*) => Some(($($v),*)),
            _ => None,
        }
    }

    #[logic(open)]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        match ($(self.$n.factor(factor.$n)),*) {
            ($(Some($v)),*) => Some(($($v),*)),
            _ => None,
        }
    }

    #[logic(open, inline)]
    #[ensures(#[trigger(self == other)] result == (self == other))]
    fn eq(self, other: Self) -> bool {
        $(self.$n.eq(other.$n))&&*
    }

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open)]
    fn core(self) -> Option<Self> {
        match ($(self.$n.core()),*) {
            ($(Some($v)),*) => Some(($($v),*)),
            _ => None,
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
        $(
            self.$n.core_idemp();
        )*
    }

    #[logic]
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self) {
        $(
            self.$n.core_is_maximal_idemp(i.$n);
        )*
    }

    ra_tuples! { @cancelation $(($n, $v))* }
}

    };

    // We use this to extract the first element
    (@cancelation ($n1:tt, $v1:ident) $(($n:tt, $v:ident))*) => {
        #[logic(open)]
        #[ensures(result == (forall<x, y> self.op(x) != None ==>
            self.op(x) == self.op(y) ==> x == y))]
        fn cancelable(self) -> bool {
            proof_assert!(
                // If there are compatible elements on each projection…
                forall<$v1, $($v),*> self.0.op($v1) != None ==> $(self.$n.op($v) != None ==>)*
                // and self is cancelable…
                (forall<x, y> self.op(x) != None ==> self.op(y) != None ==> self.op(x) == self.op(y) ==> x == y) ==>
                // then self.0 is cancelable
                forall<x, y> self.0.op(x) != None ==> self.0.op(y) != None ==>
                    self.op((x, $($v),*)) == self.op((y, $($v),*)) ==> x == y
            );
            pearlite! {
                (forall<$v1> self.0.op($v1) == None) ||
                $(
                    (forall<$v> self.$n.op($v) == None) ||
                )*
                ( self.$n1.cancelable() && $(self.$n.cancelable())&&* )
            }
        }
    };
}

ra_tuples! { (T1, 0, v1) (T2, 1, v2) }

impl<T: UnitRA, U: UnitRA> UnitRA for (T, U) {
    #[logic]
    #[ensures(forall<x: Self> #[trigger(x.op(result))] x.op(result) == Some(x))]
    fn unit() -> Self {
        (T::unit(), U::unit())
    }

    #[logic(open)]
    #[ensures(self.core() == Some(result))]
    fn core_total(self) -> Self {
        (self.0.core_total(), self.1.core_total())
    }

    #[logic]
    #[ensures(self.core_total().op(self.core_total()) == Some(self.core_total()))]
    #[ensures(self.core_total().op(self) == Some(self))]
    fn core_total_idemp(self) {
        self.0.core_total_idemp();
        self.1.core_total_idemp();
    }
}

impl<R1: RA, R2: RA, U1: Update<R1>, U2: Update<R2>> Update<(R1, R2)> for (U1, U2) {
    type Choice = (U1::Choice, U2::Choice);

    #[logic(open, inline)]
    fn premise(self, from: (R1, R2)) -> bool {
        self.0.premise(from.0) && self.1.premise(from.1)
    }

    #[logic(open, inline)]
    #[requires(self.premise(from))]
    fn update(self, from: (R1, R2), ch: (U1::Choice, U2::Choice)) -> (R1, R2) {
        (self.0.update(from.0, ch.0), self.1.update(from.1, ch.1))
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: (R1, R2), frame: (R1, R2)) -> Self::Choice {
        (self.0.frame_preserving(from.0, frame.0), self.1.frame_preserving(from.1, frame.1))
    }
}

impl<R1: RA, R2: RA, U1: LocalUpdate<R1>, U2: LocalUpdate<R2>> LocalUpdate<(R1, R2)> for (U1, U2) {
    #[logic(open, inline)]
    fn premise(self, from_auth: (R1, R2), from_frag: (R1, R2)) -> bool {
        self.0.premise(from_auth.0, from_frag.0) && self.1.premise(from_auth.1, from_frag.1)
    }

    #[logic(open, inline)]
    fn update(self, from_auth: (R1, R2), from_frag: (R1, R2)) -> ((R1, R2), (R1, R2)) {
        let (to_auth0, to_frag0) = self.0.update(from_auth.0, from_frag.0);
        let (to_auth1, to_frag1) = self.1.update(from_auth.1, from_frag.1);
        ((to_auth0, to_auth1), (to_frag0, to_frag1))
    }

    #[logic]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(self, from_auth: (R1, R2), from_frag: (R1, R2), frame: Option<(R1, R2)>) {
        self.0.frame_preserving(from_auth.0, from_frag.0, frame.map_logic(|f: (R1, R2)| f.0));
        self.1.frame_preserving(from_auth.1, from_frag.1, frame.map_logic(|f: (R1, R2)| f.1));
    }
}
