use crate::*;
use crate::logic::Set;

#[allow(unused_variables)]

pub trait RA: Sized {
    #[logic]
    fn op(self, other: Self) -> Self;

    #[logic]
    fn valid(self) -> bool;

    // Derived notions: `incl`, `idemp`.
    // We allow the implementor to give a custom definition, that is possibly
    // simpler than the generic one. The custom definition is the one that
    // will be used to prove the RA laws.

    // Following Iris, our definition of `incl` is not reflexive.
    // We could define it to be `self == other || ...`, but doing that
    // loses the following desirable property for the product RA:
    //
    //   (x, y).incl((x', y')) == x.incl(x') && y.incl(y').
    //
    // If you need the reflexive closure of the inclusion relation, then
    // you can use `Some(x).incl(Some(y))`. Indeed, `incl` on the Option RA
    // has the following property:
    //
    //  Some(x).incl(Some(y)) == (x == y || x.incl(y))
    //
    // Note that the paper on the maximal idempotent axiom uses the
    // reflexive definition of `incl` on paper, but not in its accompanying
    // Iris formalization, where it uses the non-reflexive definition (as
    // we do here).
    #[logic]
    #[ensures(result == exists<c: Self> self.op(c) == other)]
    fn incl(self, other: Self) -> bool;

    #[logic]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool;

    // Laws

    #[law]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self);

    #[law]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self);

    // TODO: should this be a #[law]?
    #[logic]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self);

    #[logic]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self);
}

#[logic]
#[open(self)]
#[requires(a.incl(b) && b.incl(c))]
#[ensures(a.incl(c))]
pub fn incl_transitive<T: RA>(a: T, b: T, c: T) { }

// TODO: make these definitions part of the trait ?
// could they have default implementations? is it useful to allow for custom definitions?

#[logic]
#[open]
pub fn update<T: RA>(x: T, y: T) -> bool { pearlite!{
    forall<z: T> x.op(z).valid() ==> y.op(z).valid()
}}

#[logic]
#[open]
pub fn update_nondet<T: RA>(x: T, s: Set<T>) -> bool { pearlite!{
    forall<z: T> x.op(z).valid() ==>
        exists<y: T> s.contains(y) && y.op(z).valid()
}}

pub mod agree;
pub mod excl;
pub mod prod;
pub mod sum;
pub mod option;
pub mod view;
pub mod auth;
pub mod fmap;

// NOTE: always require that we have Sized data in logical APIs?
// thus remove SizedW from library code; require the end user
// to manually box if they need to.
