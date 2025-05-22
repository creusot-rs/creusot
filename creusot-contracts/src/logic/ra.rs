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
///
/// We allow RAs to contain junk values and equip RAs with a validity predicate. This
/// is unlike the paper definitions of GMB (who instead take `op` to be a partial
/// function), but like in Iris and the Iris mechanization of GMB (cf the artifact of
/// the paper). This is because Creusot does not support subset types in the logic,
/// which would be required to define e.g. the Auth RA if we were to disallow junk
/// values. (The Iris formalization also makes this choice for practical formalization
/// reasons, as far as we know.)
/// The downside is that junk values pollute the definition of some RAs and higher-order
/// order agreement is harder to define (according to GMB, but we only need first-order
/// agreement in Creusot anyway). On the plus side, working with a total `op` instead of
/// chaining operations in the Option monad is often nicer.
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
    /// Note that the paper on the maximal idempotent axiom (GMB) uses the
    /// reflexive definition of `incl` on paper, but not in its accompanying
    /// Iris formalization, where it uses the non-reflexive definition (as
    /// we do here).
    #[logic]
    #[ensures(match result {
        Some(c) => self.op(c) == other,
        None => forall<c: Self> self.op(c) != other,
    })]
    fn incl(self, other: Self) -> Option<Self>;

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
    #[ensures(match result {
        Some(b) => b.incl(self) != None && b.idemp() &&
           forall<c: Self> c.incl(self) != None && c.idemp() ==> c.incl(b) != None,
        None => forall<b: Self> ! (b.incl(self) != None && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self>;
}

/// [`RA::incl`] is transitive.
// TODO: with sealed trait functions, it would be possible to pull this inside the trait as a law.
#[logic]
#[open(self)]
#[ensures(match (a.incl(b), b.incl(c)) {
    (Some(_), Some(_)) => a.incl(c) != None,
    _ => true,
})]
pub fn incl_transitive<T: RA>(a: T, b: T, c: T) {}

#[logic]
#[open]
pub fn incl_eq<T: RA>(this: T, other: T) -> Option<T> {
    if this == other { Some(this) } else { this.incl(other) }
}

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
