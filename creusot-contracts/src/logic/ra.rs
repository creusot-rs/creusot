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
    auth::{Auth, AuthViewRel},
    excl::Excl,
    sum::Sum,
    view::{View, ViewRel},
};

use crate::{logic::Set, *};

/// Define a _Resource Algebra_.
///
/// Resource algebras are a concept inspired by [Iris](https://iris-project.org/). Used in
/// conjunction with [`Resource`](crate::resource::Resource)s, they unlock new reasonings.
///
/// # Notes on the definition of resource algebras
///
/// Our definition of resource algebras differs from the one in Iris in that it
/// does not require RAs to define a "core" function. Instead, we follow "Idempotent
/// Resources in Separation Logic --- The Heart of core in Iris" by Gratzer, Møller &
/// Birkedal (GMB), and require RAs to satisfy a "maximal idempotent" axiom.
pub trait RA: Sized {
    /// The operation of this resource algebra.
    ///
    /// This is the core of the trait. This operation will be used to [`join`](crate::resource::Resource::join)
    /// and [`split`](crate::resource::Resource::split) resources.
    ///
    /// It must be [associative](Self::associative) and [commutative](Self::commutative)
    /// (among others).
    #[logic]
    fn op(self, other: Self) -> Option<Self>;

    // Derived notions: `factor`, `incl`, `idemp`.
    // We allow the implementor to give a custom definition, that is possibly
    // simpler than the generic one. The custom definition is the one that
    // will be used to prove the RA laws.

    /// Factorizing elements of the RA
    ///
    /// Given `a` and `c`, this returns an element `b` such that `a = b.c`,
    /// or returns `None` if there does not exists such an element.
    #[logic]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self>;

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
    /// Note that the paper on the maximal idempotent axiom (GMB) uses the
    /// reflexive definition of `incl` on paper, but not in its accompanying
    /// Iris formalization, where it uses the non-reflexive definition (as
    /// we do here).
    #[logic(sealed)]
    #[open]
    fn incl(self, other: Self) -> bool {
        other.factor(self) != None
    }

    #[law(sealed)]
    #[requires(self.op(other) == Some(comb))]
    #[ensures(self.incl(comb))]
    fn incl_op(self, other: Self, comb: Self) {}

    #[logic(sealed)]
    #[open]
    fn incl_eq(self, other: Self) -> bool {
        self == other || self.incl(other)
    }

    /// Identifies an element as _idempotent_.
    ///
    /// This means that this particular element can be duplicated with [`Self::op`].
    #[logic]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool;

    /// Ensures that we can go from `self` to `x` without making composition with the frame invalid.
    ///
    /// This is used in [`Resource::update`](crate::resource::Resource::update).
    #[logic(sealed)]
    #[open]
    fn update(self, x: Self) -> bool {
        pearlite! {
            forall<y: Self> self.op(y) != None ==> x.op(y) != None
        }
    }

    /// This is used in [`Resource::update_nondet`](crate::resource::Resource::update_nondet).
    #[logic(sealed)]
    #[open]
    fn update_nondet(self, s: Set<Self>) -> bool {
        pearlite! {
            forall<y: Self> self.op(y) != None ==>
                exists<x: Self> s.contains(x) && x.op(y) != None
        }
    }

    // Laws

    /// [`Self::op`] is commutative.
    #[law]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self);

    /// [`Self::op`] is associative.
    #[law]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self);

    /// [`RA::incl`] is transitive.
    #[law(sealed)]
    #[open(self)]
    #[requires(a.incl(b))]
    #[requires(b.incl(c))]
    #[ensures(a.incl(c))]
    fn incl_transitive(a: Self, b: Self, c: Self) {
        let _ = Self::associative;
    }

    /// For every element, there is a maximal (in the sense of [`Self::incl`]) part
    /// of `self` that is [`Self::idemp`].
    #[logic]
    #[ensures(match result {
        Some(b) => b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b),
        None => forall<b: Self> ! (b.incl(self) && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self>;
}

pub trait UnitRA: RA {
    #[logic]
    #[ensures(forall<x: Self> x.op(result) == Some(x))]
    fn unit() -> Self;

    #[law(sealed)]
    #[ensures(forall<x: Self> Self::unit().op(x) == Some(x))]
    fn unit_op_l() {}

    #[law(sealed)]
    #[ensures(forall<x: Self> x.incl(x))]
    fn incl_refl() {
        let _ = Self::unit();
    }

    #[law(sealed)]
    #[ensures(Self::unit().maximal_idemp() == Some(Self::unit()))]
    fn unit_maximal_idemp() {}

    #[logic]
    #[ensures(Some(result) == self.maximal_idemp())]
    #[ensures(result.incl(self))]
    #[ensures(result.idemp())]
    #[ensures(forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(result))]
    fn maximal_idemp_total(self) -> Self {
        let _ = Self::unit();
        self.maximal_idemp().unwrap_logic()
    }
}
