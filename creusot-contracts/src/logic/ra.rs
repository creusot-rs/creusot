//! Definitions of Resource Algebras

mod agree;
mod auth;
mod excl;
mod fmap;
mod option;
mod prod;
mod sum;
mod view;

pub use self::{
    agree::Ag,
    auth::Auth,
    excl::Excl,
    sum::Sum,
    view::{View, ViewRel},
};

use crate::{logic::Set, *};

/// Define a _Resource Algebra_.
///
/// Resource algebras are a concept inspired by [Iris](https://iris-project.org/). Used in
/// conjunction with [`Resource`](crate::resource::Resource)s, they unlock new reasonings.
pub trait RA: Sized {
    /// The operation of this resource algebra.
    ///
    /// This is the core of the trait. This operation will be used to [`join`](crate::resource::Resource::join)
    /// and [`split`](crate::resource::Resource::split) resources.
    ///
    /// It must be [associative](Self::associative) and [commutative](Self::commutative)
    /// (among others).
    #[logic]
    fn op(self, other: Self) -> Self;

    /// Whether the resource algebra is valid.
    ///
    /// The logic encoded in Iris ensures that [`Resource`](crate::resource::Resource)s
    /// are always valid.
    #[logic]
    fn valid(self) -> bool;

    // Derived notions: `incl`, `idemp`.
    // We allow the implementor to give a custom definition, that is possibly
    // simpler than the generic one. The custom definition is the one that
    // will be used to prove the RA laws.

    /// Inclusion of RA.
    ///
    /// This asserts that `other` is, in a sense, 'bigger' than `self`.
    ///
    /// # Notes on reflexivity
    ///
    /// Following Iris, our definition of `incl` is not reflexive.
    /// We could define it to be `self == other || ...`, but doing that
    /// loses the following desirable property for the product RA:
    ///
    /// ```text
    /// (x, y).incl((x', y')) == x.incl(x') && y.incl(y').
    /// ```
    ///
    /// If you need the reflexive closure of the inclusion relation, then
    /// you can use `Some(x).incl(Some(y))`. Indeed, `incl` on the Option RA
    /// has the following property:
    ///
    /// ```text
    /// Some(x).incl(Some(y)) == (x == y || x.incl(y))
    /// ```
    ///
    /// Note that the paper on the maximal idempotent axiom uses the
    /// reflexive definition of `incl` on paper, but not in its accompanying
    /// Iris formalization, where it uses the non-reflexive definition (as
    /// we do here).
    #[logic]
    #[ensures(result == exists<c: Self> self.op(c) == other)]
    fn incl(self, other: Self) -> bool;

    /// Identifies an element as _idempotent_.
    ///
    /// This means that this particular element can be duplicated with [`Self::op`].
    #[logic]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool;

    // Laws

    /// [`Self::op`] is commutative.
    #[law]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self);

    /// [`Self::op`] is associative.
    #[law]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self);

    /// Validity cannot be lost by splitting a resource.
    #[logic]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self);

    /// For every element, there is a maximal (in the sense of [`Self::incl`]) part
    /// of `self` that is [`Self::idemp`].
    #[logic]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self);
}

/// [`RA::incl`] is transitive.
// TODO: with sealed trait functions, it would be possible to pull this inside the trait as a law.
#[logic]
#[open(self)]
#[requires(a.incl(b) && b.incl(c))]
#[ensures(a.incl(c))]
pub fn incl_transitive<T: RA>(a: T, b: T, c: T) {}

/// Ensures that we can go from `x` to `y` without making composition with the frame invalid.
///
/// This is used in [`Resource::update`](crate::resource::Resource::update).
#[logic]
#[open]
pub fn update<T: RA>(x: T, y: T) -> bool {
    pearlite! {
        forall<z: T> x.op(z).valid() ==> y.op(z).valid()
    }
}

/// This is used in [`Resource::update_nondet`](crate::resource::Resource::update_nondet).
#[logic]
#[open]
pub fn update_nondet<T: RA>(x: T, s: Set<T>) -> bool {
    pearlite! {
        forall<z: T> x.op(z).valid() ==>
            exists<y: T> s.contains(y) && y.op(z).valid()
    }
}
