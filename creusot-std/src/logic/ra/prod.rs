use crate::{
    logic::ra::{
        RA, UnitRA,
        update::{LocalUpdate, Update},
    },
    prelude::*,
};

macro_rules! ra_tuples {
    ($(($t:ident, $n:tt, $v:ident, $r:ident))*) => {

impl<$($t : RA),*> RA for ($($t),*) {
    #[logic(open)]
    fn op(self, other: Self) -> Option<Self> {
        match ($(self.$n.op(other.$n)),*) {
            ($(Some($v)),*) => Some(($($v),*)),
            _ => None,
        }
    }

    #[logic(open)]
    fn incl(self, other: Self) -> bool {
        $(self.$n.incl(other.$n))&&*
    }

    #[logic(open, inline)]
    #[ensures(#[trigger(self == other)] result == (self == other))]
    fn eq(self, other: Self) -> bool {
        $(self.$n.eq(other.$n))&&*
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[allow(unused_variables)]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open)]
    fn core(self) -> Option<Self> {
        match ($(self.$n.core()),*) {
            ($(Some($v)),*) => Some(($($v),*)),
            _ => None,
        }
    }

    #[logic]
    fn core_idemp(self) {
        $(
            self.$n.core_idemp();
        )*
    }

    #[logic]
    fn core_is_maximal_idemp(self, i: Self) {
        $(
            self.$n.core_is_maximal_idemp(i.$n);
        )*
    }

    ra_tuples! { @cancelation $(($n, $v))* }
}

impl<$($t : UnitRA),*> UnitRA for ($($t),*) {
    #[logic]
    fn unit() -> Self {
        ($($t::unit()),*)
    }

    #[logic(open)]
    fn core_total(self) -> Self {
        ($(self.$n.core_total()),*)
    }

    #[logic]
    fn core_total_idemp(self) {
        $(
            self.$n.core_total_idemp();
        )*
    }
}

impl<$($r : RA),* , $($t : Update<$r>),*> Update<($($r),*)> for ($($t),*) {
    type Choice = ($($t::Choice),*);

    #[logic(open, inline)]
    fn premise(self, from: ($($r),*)) -> bool {
        $(
            self.$n.premise(from.$n)
        )&&*
    }

    #[logic(open, inline)]
    #[requires(self.premise(from))]
    fn update(self, from: ($($r),*), ch: Self::Choice) -> ($($r),*) {
        ($(self.$n.update(from.$n, ch.$n)),*)
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: ($($r),*), frame: ($($r),*)) -> Self::Choice {
        ( $(
            self.$n.frame_preserving(from.$n, frame.$n)
        ),* )
    }
}

impl<$($r : RA),* , $($t : LocalUpdate<$r>),*> LocalUpdate<($($r),*)> for ($($t),*) {
    #[logic(open, inline)]
    fn premise(self, from_auth: ($($r),*), from_frag: ($($r),*)) -> bool {
        $(
            self.$n.premise(from_auth.$n, from_frag.$n)
        )&&*
    }

    #[logic(open, inline)]
    fn update(self, from_auth: ($($r),*), from_frag: ($($r),*)) -> (($($r),*), ($($r),*)) {
        $(
            let $v = self.$n.update(from_auth.$n, from_frag.$n);
        )*
        (($($v.0),*), ($($v.1),*))
    }

    ra_tuples! { @local_upd_frame_preserve
        type_r: $($r)* ;
        list: $(($n, $v))* ;
        with_type_r: ;
    }

}

    };

    // We use this to repeat the type ($($r),*) at a lower level
    (@local_upd_frame_preserve
        type_r: $($r:ident)* ;
        list: ($n1:tt, $v1:ident) $(($n_t:tt, $v_t:tt))* ;
        with_type_r: $(($n:tt, $v:ident, $t:ty))* ;
    ) => {
        ra_tuples! { @local_upd_frame_preserve
            type_r: $($r)* ;
            list: $(($n_t, $v_t))* ;
            with_type_r: $(($n, $v, $t))* ($n1, $v1, ($($r),*)) ;
        }
    };

    (@local_upd_frame_preserve
        type_r: $($r:ident)* ;
        list: ;
        with_type_r: $(($n:tt, $v:ident, $t:ty))* ;
    ) => {
        #[logic]
        #[requires(self.premise(from_auth, from_frag))]
        #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
        #[ensures({
            let (to_auth, to_frag) = self.update(from_auth, from_frag);
            Some(to_frag).op(frame) == Some(Some(to_auth))
        })]
        fn frame_preserving(self, from_auth: ($($r),*), from_frag: ($($r),*), frame: Option<($($r),*)>) {
            $(
                self.$n.frame_preserving(from_auth.$n, from_frag.$n, frame.map_logic(|f: $t| f.$n));
            )*
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

ra_tuples! { (T1, 0, v1, R1) (T2, 1, v2, R2) }
ra_tuples! { (T1, 0, v1, R1) (T2, 1, v2, R2) (T3, 2, v3, R3) }
ra_tuples! { (T1, 0, v1, R1) (T2, 1, v2, R2) (T3, 2, v3, R3) (T4, 3, v4, R4) }
// FIXME: the proof is too difficult for these tuples
// ra_tuples! { (T1, 0, v1) (T2, 1, v2) (T3, 2, v3) (T4, 3, v4) (T5, 4, v5) }
// ra_tuples! { (T1, 0, v1) (T2, 1, v2) (T3, 2, v3) (T4, 3, v4) (T5, 4, v5) (T6, 5, v6) }
// ra_tuples! { (T1, 0, v1) (T2, 1, v2) (T3, 2, v3) (T4, 3, v4) (T5, 4, v5) (T6, 5, v6) (T7, 6, v7) }
// ra_tuples! { (T1, 0, v1) (T2, 1, v2) (T3, 2, v3) (T4, 3, v4) (T5, 4, v5) (T6, 5, v6) (T7, 6, v7) (T8, 7, v8) }
