use crate::*;
use crate::logic::FMap;

#[allow(unused_variables)]

pub trait RA: Sized {
    #[logic]
    fn op(self, other: Self) -> Option<Self>;

    #[law]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self);

    #[law]
    #[ensures(
        a.op(b).and_then_logic(|x:Self| x.op(c)) ==
        b.op(c).and_then_logic(|x:Self| a.op(x))
    )]
    fn associative(a: Self, b: Self, c: Self);

    #[logic]
    #[ensures(
        (forall<b: Self> ! (b.le(self) && b.idemp())) ||
        (exists<b: Self> b.le(self) && b.idemp() &&
           forall<c: Self> c.le(self) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(self);

    // Derived notions and properties: `le`, `idemp`.
    // Allow the implementor to give a custom definition, that is possibly
    // simpler than the generic one. The custom definition is the one that
    // will be used to prove the RA laws.

    // Following Iris, our definition of `le` is not reflexive.
    // We could define it to be `self == other || ...`, but doing that
    // loses the following desirable property for the product RA:
    //
    //   (x, y).le((x', y')) == x.le(x') && y.le(y').
    //
    // If you need the reflexive closure of the inclusion relation, then
    // you can use `Some(x).le(Some(y))`. Indeed, `le` on the Option RA
    // has the following property:
    //
    //  Some(x).le(Some(y)) == (x == y || x.le(y))
    //
    // Note that the paper on the maximal idempotent axiom uses the
    // reflexive definition of `le` on paper, but not in its accompanying
    // Iris formalization, where it uses the non-reflexive definition (as
    // we do here).
    #[logic]
    #[ensures(result == exists<c: Self> self.op(c) == Some(other))]
    fn le(self, other: Self) -> bool;

    #[logic]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool;

    // `le` is a preorder

    // #[logic]
    // #[ensures(a.le(a))]
    // // #[final]
    // #[open(self)]
    // fn le_refl(a: Self) { }

    // #[logic]
    // #[requires(a.le(b) && b.le(c))]
    // #[ensures(a.le(c))]
    // // #[final]
    // #[open(self)]
    // fn le_trans<T: RA>(a: T, b: T, c: T) { }

    // TODO: prédicat fupd
}

pub struct Excl<T>(pub T);

impl<T> RA for Excl<T>
    where T: RA
{
    #[logic]
    #[open]
    fn op(self, _other: Self) -> Option<Self> {
        None
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == Some(other)))]
    fn le(self, other: Self) -> bool {
        false
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        false
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(
        a.op(b).and_then_logic(|x:Self| x.op(c)) ==
        b.op(c).and_then_logic(|x:Self| a.op(x))
    )]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(
        (forall<b: Self> ! (b.le(self) && b.idemp())) ||
        (exists<b: Self> b.le(self) && b.idemp() &&
           forall<c: Self> c.le(self) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(self) { }
}

pub struct Ag<T>(pub T);

impl<T> RA for Ag<T>
    where T: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        if self == other {
            Some(self)
        } else {
            None
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        true
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == Some(other)))]
    fn le(self, other: Self) -> bool {
        self == other
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(
        a.op(b).and_then_logic(|x:Self| x.op(c)) ==
        b.op(c).and_then_logic(|x:Self| a.op(x))
    )]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(
        (forall<b: Self> ! (b.le(self) && b.idemp())) ||
        (exists<b: Self> b.le(self) && b.idemp() &&
           forall<c: Self> c.le(self) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(self) { }
}

impl<T, U> RA for (T, U)
    where T: RA, U: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> { pearlite!{
        self.0.op(other.0).and_then_logic(|x:T| {
            self.1.op(other.1).and_then_logic(|y:U| {
                Some((x, y))
            })
        })
    }}

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == Some(other)))]
    fn le(self, other: Self) -> bool {
        if self.0.le(other.0) && self.1.le(other.1) {
            proof_assert!(exists<c0: T, c1: U>
              self.0.op(c0) == Some(other.0) &&
              self.1.op(c1) == Some(other.1) &&
              self.op((c0, c1)) == Some(other)
            )
        }
        self.0.le(other.0) && self.1.le(other.1)
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        self.0.idemp() && self.1.idemp()
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(
        a.op(b).and_then_logic(|x:Self| x.op(c)) ==
        b.op(c).and_then_logic(|x:Self| a.op(x))
    )]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(
        (forall<b: Self> ! (b.le(self) && b.idemp())) ||
        (exists<b: Self> b.le(self) && b.idemp() &&
           forall<c: Self> c.le(self) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(self) {
        self.0.maximal_idemp();
        self.1.maximal_idemp();
    }
}

pub enum Sum<T, U> {
    Left(T),
    Right(U),
}

#[allow(unused_imports)]
use Sum::{Left, Right};

impl<T, U> RA for Sum<T, U>
    where T: RA, U: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Left(x), Left(y)) => x.op(y).and_then_logic(|z| Some(Left(z))),
            (Right(x), Right(y)) => x.op(y).and_then_logic(|z| Some(Right(z))),
            (_, _) => None,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == Some(other)))]
    fn le(self, other: Self) -> bool {
        match (self, other) {
            (Left(x), Left(y)) => x.le(y),
            (Right(x), Right(y)) => x.le(y),
            (_, _) => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        match self {
            Left(x) => x.idemp(),
            Right(x) => x.idemp(),
        }
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(
        a.op(b).and_then_logic(|x:Self| x.op(c)) ==
        b.op(c).and_then_logic(|x:Self| a.op(x))
    )]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(
        (forall<b: Self> ! (b.le(self) && b.idemp())) ||
        (exists<b: Self> b.le(self) && b.idemp() &&
           forall<c: Self> c.le(self) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(self) {
        match self {
            Left(x) => x.maximal_idemp(),
            Right(x) => x.maximal_idemp(),
        }
    }
}

impl<T> RA for Option<T>
    where T: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> { pearlite!{
        match (self, other) {
            (None, _) => Some(other),
            (_, None) => Some(self),
            (Some(x), Some(y)) => x.op(y).and_then_logic(|z| Some(Some(z))),
        }
    }}

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == Some(other)))]
    fn le(self, other: Self) -> bool {
        match (self, other) {
            (None, _) => true,
            (_, None) => false,
            (Some(x), Some(y)) => {
                x == y || x.le(y)
            }
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        match self {
            None => true,
            Some(x) => x.idemp(),
        }
    }

    #[logic]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        let _ = <T as RA>::commutative;
    }

    #[law]
    #[open(self)]
    #[ensures(
        a.op(b).and_then_logic(|x:Self| x.op(c)) ==
        b.op(c).and_then_logic(|x:Self| a.op(x))
    )]
    fn associative(a: Self, b: Self, c: Self) { pearlite!{
        match (a, b, c) {
            (None, _, _) => {},
            (_, None, _) => {},
            (_, _, None) => {},
            (Some(aa), Some(bb), Some(cc)) => {
                <T as RA>::associative(aa, bb, cc)
            }
        }
    }}

    #[logic]
    #[open(self)]
    #[ensures(
        (forall<b: Self> ! (b.le(self) && b.idemp())) ||
        (exists<b: Self> b.le(self) && b.idemp() &&
           forall<c: Self> c.le(self) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(self) { pearlite!{
        match self {
            None => (),
            Some(x) => {
                x.maximal_idemp();
                if forall<y: T> ! (y.le(x) && y.idemp()) {
                    // pick None
                    proof_assert!(None.le(self) && None::<T>.idemp());
                    proof_assert!(forall<c: Self> c.le(self) && c.idemp() ==> c.le(None));
                }
            }
        }
    }}
}

// always require that we have Sized data in logical APIs?
// thus remove SizedW from library code; require the end user
// to manually box if they need to.

// impl<K, V> RA for FMap<K, V>
//     where V: RA
// {
//     #[logic]
//     #[open]
//     fn op(self, other: Self) -> Option<Self> {
//         self.merge_common(other, |(x, y): (V, V)| x.op(y))
//     }

//     #[logic]
//     #[open]
//     #[ensures(result == (self == other || exists<c: Self> self.op(c) == Some(other)))]
//     fn le(self, other: Self) -> bool { pearlite!{
//         let res: bool =
//           forall<k: K>
//             match (self.get(k), other.get(k)) {
//               (None, _) => true,
//               (Some(_), None) => false,
//               (Some(x), Some(y)) => x.le(y),
//             };

//         if res {
//             let c =
//                 other.fmapi(|(k, y)| {
//                     match self.get(k) {
//                         None => Some(y),
//                         Some(x) => {
//                             if x == y {
//                                 None
//                             } else {
//                                 // XXX how do we prove the precondition?
//                                 Some(such_that(|z: V| x.op(z) == Some(y)))
//                             }
//                         }
//                     }
//                 });
//             match self.op(c) {
//                 None => proof_assert!(false),
//                 Some(other2) => {
//                     let _ = other2.ext_eq(other);
//                     proof_assert!{ self.op(c) == Some(other) } // by {
//                     //     other2.ext_eq(other)
//                     // }
//                 }
//             }
//         } else {
//             if self == other {
//                 ()
//             } else {
//                 let c = such_that(|c| self.op(c) == Some(other));
//                 take<k: K> /* self.get(k) == None || exists<x, z> self.get(k) == Some(x) && other.get(k) == Some(z) && x.le(z) */ {
//                   match (self.get(k), self.get(c)) {
//                     (None, _) => (),
//                     (Some(x), None) => {
//                       proof_assert!{ other.get(k) == Some(x) };
//                       proof_assert!{ x.le(x) };
//                     },
//                     (Some(x), Some(y)) => {
//                       proof_assert!{ exists<z: V> x.op(y) == Some(z) && other.get(k) == Some(z) };
//                       proof_assert!{ x.le(z) };
//                     }
//                   }
//                 }
//             }
//             proof_assert!(res)
//         }

//         res
//     }}

//     #[logic]
//     #[open]
//     #[ensures(result == (self.op(self) == Some(self)))]
//     fn idemp(self) -> bool {
//         true // TODO
//     }

//     #[logic]
//     #[open(self)]
//     #[ensures(a.op(b) == b.op(a))]
//     fn commutative(a: Self, b: Self) {
//         // TODO
//     }

//     #[logic]
//     #[open(self)]
//     #[ensures(
//         a.op(b).and_then_logic(|x:Self| x.op(c)) ==
//         b.op(c).and_then_logic(|x:Self| a.op(x))
//     )]
//     fn associative(a: Self, b: Self, c: Self) { pearlite!{
//         // TODO
//     }}

//     #[logic]
//     #[open(self)]
//     #[ensures(
//         (forall<b: Self> ! (b.le(a) && b.idemp())) ||
//         (exists<b: Self> b.le(a) && b.idemp() &&
//            forall<c: Self> c.le(a) && c.idemp() ==> c.le(b))
//     )]
//     fn maximal_idemp(a: Self) {
//         // TODO
//     }
// }
