//! Definitions of Resource Algebras

pub mod agree;
pub mod auth;
pub mod excl;
pub mod fmap;
pub mod option;
pub mod prod;
pub mod sum;
pub mod update;
pub mod view;

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

    #[logic(sealed)]
    #[open]
    fn incl_eq_op(a: Self, b: Self, x: Self) -> bool {
        match a.op(b) {
            None => false,
            Some(ab) => ab.incl_eq(x),
        }
    }

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

    /// The core of an element, when it exists, is included in that element,
    /// and idempotent. Note that the statement `c.op(self) == Some(self)` is
    /// equivalent to `c.incl(self)` for idempotent elements.
    #[logic]
    #[ensures(match result {
        Some(c) => c.op(c) == Some(c) && c.op(self) == Some(self),
        None => true
    })]
    fn core(self) -> Option<Self>;

    /// The core maximal, if there exists an idempotent element included in self
    #[logic]
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self);
}

pub trait UnitRA: RA {
    #[logic]
    #[ensures(forall<x: Self> #[trigger(x.op(result))] x.op(result) == Some(x))]
    fn unit() -> Self;

    #[law(sealed)]
    #[ensures(forall<x: Self> x.incl(x))]
    fn incl_refl() {
        let _ = Self::unit();
    }

    #[law(sealed)]
    #[ensures(Self::unit().core_total() == Self::unit())]
    fn unit_core() {}

    #[logic]
    #[open]
    #[ensures(result.op(result) == Some(result))]
    #[ensures(result.op(self) == Some(self))]
    fn core_total(self) -> Self {
        let _ = self.core_is_maximal_idemp(Self::unit());
        self.core().unwrap_logic()
    }

    #[logic] // TODO: make this a law
    #[ensures(self.core() == Some(self.core_total()))]
    fn core_is_total(self);
}
