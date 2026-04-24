//! Encoding of Rustbelt's _lifetime logic_ in Creusot.
//!
//! The main types are [`FullBorrow`] and [`LifetimeToken`]; the first is
//! a mutable borrow whose lifetime is tracked by Creusot rather than by the
//! compiler. This lifetime is represented by a `LifetimeToken` object.

use creusot_std::{
    ghost::{Plain, resource::Resource},
    logic::{Id, real::PositiveReal},
    prelude::*,
};

/// Abstract representation of a lifetime.
///
/// Used to identify a lifetime in [`LifetimeToken`] and [`LifetimeDead`].
///
/// To differentiate this from a normal Rust lifetime (e.g. `'a`), we call the
/// former a _syntactic_ lifetime, while this is a _synthetic_ lifetime.
#[derive(Copy)]
pub struct Lifetime(Id);

impl Clone for Lifetime {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl Plain for Lifetime {
    #[check(ghost)]
    #[ensures(*result == *snap)]
    #[allow(unused_variables)]
    fn into_ghost(snap: Snapshot<Self>) -> Ghost<Self> {
        let s: Snapshot<Id> = snapshot!(snap.0);
        ghost!(Self(s.into_ghost().into_inner()))
    }
}

/// A token signaling that the corresponding lifetime is still active.
///
/// This token is not duplicable, but it may be [split](Self::split) into
/// multiple other tokens. Each token has an associated [fraction](Self::frac);
/// if it is `1`, the lifetime may be [killed](LifetimeDead) to end borrows made
/// at this lifetime.
///
/// This type is purely ghost, and all operations on its values compile to no-ops.
pub struct LifetimeToken(Ghost<Resource<PositiveReal>>);

impl LifetimeToken {
    /// The fraction owned by this particular token.
    ///
    /// If the token owns the full fraction (`1`), it can be used to end the
    /// lifetime.
    #[logic]
    pub fn frac(self) -> PositiveReal {
        self.0.val()
    }

    /// The lifetime identifier associated with this particular token.
    ///
    /// Only tokens with the same lifetime can be combined.
    #[logic]
    pub fn lft(self) -> Lifetime {
        Lifetime(self.0.id())
    }

    /// Get a full lifetime token for a fresh lifetime.
    #[check(ghost)]
    #[ensures(result.frac() == PositiveReal::from_int(1))]
    pub fn new() -> Self {
        Self(Resource::alloc(snapshot!(PositiveReal::from_int(1))))
    }

    /// Split a lifetime token into two tokens, by dividing its fraction by 2.
    #[check(ghost)]
    #[ensures(result.0.lft() == self.lft() && result.1.lft() == self.lft())]
    #[ensures(result.0.frac() + result.1.frac() == self.frac())]
    #[ensures(result.0.frac() == self.frac() / PositiveReal::from_int(2)
           && result.1.frac() == self.frac() / PositiveReal::from_int(2))]
    pub fn split(self) -> (Self, Self) {
        let (r1, r2) = ghost! {
            let q = snapshot!(self.frac() / PositiveReal::from_int(2));
            self.0.into_inner().split(q, q)
        }
        .split();
        (Self(r1), Self(r2))
    }

    /// Split a lifetime token from this token, by removing half of the token's
    /// fraction and giving it to the result.
    #[check(ghost)]
    #[ensures(result.lft() == self.lft() && (^self).lft() == (*self).lft())]
    #[ensures(result.frac() + (^self).frac() == self.frac())]
    #[ensures(result.frac() == self.frac() / PositiveReal::from_int(2) && (^self).frac() == self.frac() / PositiveReal::from_int(2))]
    pub fn split_off(&mut self) -> Self {
        Self(ghost! {
            let half = snapshot!(self.frac() / PositiveReal::from_int(2));
            self.0.split_off(half, half)
        })
    }

    /// Combine two lifetime tokens together, adding their fractions.
    #[check(ghost)]
    #[requires(self.lft() == other.lft())]
    #[ensures(result.lft() == self.lft())]
    #[ensures(result.frac() == self.frac() + other.frac())]
    pub fn join(self, other: Self) -> Self {
        Self(ghost!(self.0.into_inner().join(other.0.into_inner())))
    }

    /// Same as [Self::join], but with a mutable borrow.
    #[check(ghost)]
    #[requires(self.lft() == other.lft())]
    #[ensures((^self).lft() == self.lft())]
    #[ensures((^self).frac() == self.frac() + other.frac())]
    pub fn join_in(&mut self, other: Self) {
        ghost! { self.0.join_in(other.0.into_inner()) };
    }

    /// Terminates the lifetime, giving back a 'dead' token.
    #[check(ghost)]
    #[requires(self.frac() == PositiveReal::from_int(1))]
    #[ensures(result.lft() == self.lft())]
    pub fn end(self) -> LifetimeDead {
        LifetimeDead(snapshot!(self.lft()))
    }
}

impl Default for LifetimeToken {
    #[check(ghost)]
    #[ensures(result.frac() == PositiveReal::from_int(1))]
    fn default() -> Self {
        Self::new()
    }
}

/// A [lifetime](LifetimeToken) that has expired.
///
/// This token is freely duplicable.
///
/// It may be used to [get back](EndBorrow::get) the value that was originally
/// borrowed.
#[derive(Copy)]
pub struct LifetimeDead(Snapshot<Lifetime>);

impl Clone for LifetimeDead {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl LifetimeDead {
    /// The lifetime associated with this particular token.
    #[logic]
    pub fn lft(self) -> Lifetime {
        *self.0
    }
}

/// A mutable borrow, with a synthetic lifetime.
///
/// Correct usage of this borrow (e.g. non-aliasing) is checked by respecting
/// the contracts of the associated functions.
///
/// Objects of this type may only be [constructed in ghost](FullBorrow::new).
pub struct FullBorrow<T> {
    ptr: *mut T,
}

/// Container for the final value of a [`FullBorrow`].
///
/// Can be used to get back the original value once the lifetime of the borrow
/// is finished, by using [`EndBorrow::get`].
#[opaque]
pub struct EndBorrow<T>(::core::marker::PhantomData<*mut T>);

impl<T> creusot_std::logic::ops::Fin for FullBorrow<T> {
    type Target = T;

    #[logic(opaque, prophetic)]
    fn fin<'a>(self) -> &'a T {
        dead
    }
}

impl<T> Resolve for FullBorrow<T> {
    #[logic(open, prophetic)]
    fn resolve(self) -> bool {
        pearlite! { self.cur() == ^self }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(inv(self))]
    #[requires(creusot_std::resolve::structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<T> FullBorrow<T> {
    /// The lifetime of this borrow
    #[logic(opaque)]
    pub fn lft(self) -> Lifetime {
        dead
    }

    /// The current value of this borrow.
    #[logic(opaque)]
    pub fn cur(self) -> T {
        dead
    }

    /// The final value of this borrow.
    ///
    /// Also accessible with the final operator `^`.
    #[logic(open, prophetic)]
    pub fn fin(self) -> T {
        pearlite! { ^self }
    }

    /// Create a new full borrow of the value `x`.
    ///
    /// Note that it also gives back a value of type [`EndBorrow`], that
    /// can be used to get back the original value once the lifetime of the
    /// borrow has ended.
    ///
    /// # in Rustbelt
    ///
    /// This is the 'LftL-borrow' rule.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.0.cur() == *x)]
    #[ensures(result.0.lft() == *lft && result.1.lft() == *lft)]
    #[ensures(^result.0 == ^result.1)]
    #[allow(unused_variables)]
    pub fn new(x: Ghost<T>, lft: Snapshot<Lifetime>) -> (Ghost<Self>, Ghost<EndBorrow<T>>) {
        (Ghost::conjure(), Ghost::conjure())
    }

    /// Get an immutable borrow to read the value.
    ///
    /// The `token` object ensures that the lifetime of the `FullBorrow` has not
    /// expired yet.
    #[trusted]
    #[check(ghost)]
    #[requires(self.lft() == token.lft())]
    #[ensures(*result == self.cur())]
    #[allow(unused_variables)]
    pub fn borrow<'a>(&'a self, token: &'a LifetimeToken) -> &'a T {
        unsafe { &*self.ptr }
    }

    /// Get a mutable borrow to write into the value.
    ///
    /// The `token` object ensures that the lifetime of the `FullBorrow` has not
    /// expired yet.
    ///
    /// Functionally equivalent to a reborrow.
    ///
    /// # In Rustbelt
    ///
    /// This is the rule 'LftL-bor-unnest' (but mixed between syntactic and
    /// synthetic lifetimes).
    #[trusted]
    #[check(ghost)]
    #[requires(self.lft() == token.lft())]
    #[ensures((^self).lft() == self.lft())]
    #[ensures(^^self == ^*self)]
    #[ensures((*self).cur() == *result && (^self).cur() == ^result)]
    #[allow(unused_variables)]
    pub fn borrow_mut<'a>(&'a mut self, token: &'a LifetimeToken) -> &'a mut T {
        unsafe { &mut *self.ptr }
    }

    /// Change the type of a full borrow.
    ///
    /// This is similar to [`std::cell::RefMut::map`].
    #[trusted]
    #[check(ghost)]
    #[requires(self.lft() == token.lft())]
    #[requires(forall<b: &mut T> *b == self.cur() && ^b == ^self ==>
        f.precondition((b,)))]
    #[ensures(exists<b: &mut T, res: &mut U>
        *b == self.cur() && ^b == ^self && *res == result.cur() && ^res == ^result &&
        f.postcondition_once((b,), res)
    )]
    #[ensures(result.lft() == self.lft())]
    #[allow(unused_variables)]
    pub fn map<U, F>(self, f: F, token: &LifetimeToken) -> FullBorrow<U>
    where
        F: for<'a> FnOnce(&'a mut T) -> &'a mut U,
    {
        FullBorrow { ptr: self.ptr.cast() }
    }
}

macro_rules! tuple_split {
    ( $map_split:ident $( ($name:ident, $idx:tt) )+ ) => {
        impl<$($name),+> FullBorrow<($($name,)+)> {
            // FIXME: docs
            #[trusted]
            #[check(ghost)]
            $(
                #[ensures(result.$idx.lft() == self.lft())]
                #[ensures(result.$idx.cur() == self.cur().$idx && ^result.$idx == (^self).$idx)]
            )+
            pub fn split(self) -> ($(FullBorrow<$name>,)+){
                unreachable!("ghost code only")
            }
        }

        impl<T0> FullBorrow<T0> {
            #[trusted]
            #[check(ghost)]
            #[requires(self.lft() == token.lft())]
            #[requires(forall<b: &mut T0> *b == self.cur() && ^b == ^self ==>
                f.precondition((b,)))]
            #[ensures(exists<b: &mut T0, res: ($(&mut $name,)+)>
                *b == self.cur() && ^b == ^self &&
                $(*res.$idx == result.$idx.cur() && ^res.$idx == ^result.$idx &&)+
                f.postcondition_once((b,), res)
            )]
            $(
                #[ensures(result.$idx.lft() == self.lft())]
            )+
            #[allow(unused_variables)]
            pub fn $map_split<$($name,)+ F>(self, f: F, token: &LifetimeToken) -> ($(FullBorrow<$name>,)+)
            where
                F: for<'a> FnOnce(&'a mut T0) -> ($(&'a mut $name,)+),
            {
                unreachable!("ghost code only")
            }
        }
    };
}

tuple_split! { map_split_1  (T,0) }
tuple_split! { map_split_2  (U,0) (T,1) }
tuple_split! { map_split_3  (V,0) (U,1) (T,2) }
tuple_split! { map_split_4  (W,0) (V,1) (U,2) (T,3) }
tuple_split! { map_split_5  (X,0) (W,1) (V,2) (U,3) (T,4) }
tuple_split! { map_split_6  (Y,0) (X,1) (W,2) (V,3) (U,4) (T,5) }
tuple_split! { map_split_7  (Z,0) (Y,1) (X,2) (W,3) (V,4) (U,5) (T,6) }
tuple_split! { map_split_8  (A,0) (Z,1) (Y,2) (X,3) (W,4) (V,5) (U,6) (T,7) }
tuple_split! { map_split_9  (B,0) (A,1) (Z,2) (Y,3) (X,4) (W,5) (V,6) (U,7) (T,8) }
tuple_split! { map_split_10 (C,0) (B,1) (A,2) (Z,3) (Y,4) (X,5) (W,6) (V,7) (U,8) (T,9) }
tuple_split! { map_split_11 (D,0) (C,1) (B,2) (A,3) (Z,4) (Y,5) (X,6) (W,7) (V,8) (U,9) (T,10) }
tuple_split! { map_split_12 (E,0) (D,1) (C,2) (B,3) (A,4) (Z,5) (Y,6) (X,7) (W,8) (V,9) (U,10) (T,11) }

impl<T> creusot_std::logic::ops::Fin for EndBorrow<T> {
    type Target = T;
    #[logic(opaque, prophetic)]
    fn fin<'a>(self) -> &'a T {
        dead
    }
}

impl<T> EndBorrow<T> {
    /// Lifetime associated with the corresponding borrow.
    #[logic(opaque)]
    pub fn lft(self) -> Lifetime {
        dead
    }

    /// Get back the original value used to create the corresponding borrow.
    #[trusted]
    #[check(ghost)]
    #[requires(self.lft() == lft_dead.lft())]
    #[ensures(result == ^self)]
    #[allow(unused_variables)]
    pub fn get(self, lft_dead: LifetimeDead) -> T {
        unreachable!("ghost code only")
    }
}
