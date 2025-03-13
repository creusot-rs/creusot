use crate::*;
// use crate::logic::FMap;
// use crate::util::*;

#[allow(unused_variables)]

pub trait RA: Sized {
    #[logic]
    fn op(self, other: Self) -> Option<Self>;

    #[logic]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self);

    #[logic]
    #[ensures(
        a.op(b).and_then_logic(|x:Self| x.op(c)) ==
        b.op(c).and_then_logic(|x:Self| a.op(x))
    )]
    fn associative(a: Self, b: Self, c: Self);

    #[logic]
    #[ensures(
        (forall<b: Self> ! (b.le(a) && b.idemp())) ||
        (exists<b: Self> b.le(a) && b.idemp() &&
           forall<c: Self> c.le(a) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(a: Self);

    // Derived notions and properties: `le`, `idemp`.
    // Allow the implementor to give a custom definition, that is possibly
    // simpler than the generic one. The custom definition is the one that
    // will be used to prove the RA laws.

    #[logic]
    #[ensures(result == (self == other || exists<c: Self> self.op(c) == Some(other)))]
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

// pub struct Excl<T>(pub T);

// impl<T> RA for Excl<T>
//     where T: RA
// {
//     #[logic]
//     #[open]
//     fn op(self, _other: Self) -> Option<Self> {
//         None
//     }

//     #[logic]
//     #[open]
//     #[ensures(result == (self == other || exists<c: Self> self.op(c) == Some(other)))]
//     fn le(self, other: Self) -> bool {
//         self == other
//     }

//     #[logic]
//     #[open]
//     #[ensures(result == (self.op(self) == Some(self)))]
//     fn idemp(self) -> bool {
//         false
//     }

//     #[logic]
//     #[open(self)]
//     #[ensures(a.op(b) == b.op(a))]
//     fn commutative(a: Self, b: Self) { }

//     #[logic]
//     #[open(self)]
//     #[ensures(
//         a.op(b).and_then_logic(|x:Self| x.op(c)) ==
//         b.op(c).and_then_logic(|x:Self| a.op(x))
//     )]
//     fn associative(a: Self, b: Self, c: Self) { }

//     #[logic]
//     #[open(self)]
//     #[ensures(
//         (forall<b: Self> ! (b.le(a) && b.idemp())) ||
//         (exists<b: Self> b.le(a) && b.idemp() &&
//            forall<c: Self> c.le(a) && c.idemp() ==> c.le(b))
//     )]
//     fn maximal_idemp(a: Self) { }
// }

// pub struct Ag<T>(pub T);

// impl<T> RA for Ag<T>
//     where T: RA
// {
//     #[logic]
//     #[open]
//     fn op(self, other: Self) -> Option<Self> {
//         if self == other {
//             Some(self)
//         } else {
//             None
//         }
//     }

//     #[logic]
//     #[open]
//     #[ensures(result == (self.op(self) == Some(self)))]
//     fn idemp(self) -> bool {
//         true
//     }

//     #[logic]
//     #[open]
//     #[ensures(result == (self == other || exists<c: Self> self.op(c) == Some(other)))]
//     fn le(self, other: Self) -> bool {
//         self == other
//     }

//     #[logic]
//     #[open(self)]
//     #[ensures(a.op(b) == b.op(a))]
//     fn commutative(a: Self, b: Self) { }

//     #[logic]
//     #[open(self)]
//     #[ensures(
//         a.op(b).and_then_logic(|x:Self| x.op(c)) ==
//         b.op(c).and_then_logic(|x:Self| a.op(x))
//     )]
//     fn associative(a: Self, b: Self, c: Self) { }

//     #[logic]
//     #[open(self)]
//     #[ensures(
//         (forall<b: Self> ! (b.le(a) && b.idemp())) ||
//         (exists<b: Self> b.le(a) && b.idemp() &&
//            forall<c: Self> c.le(a) && c.idemp() ==> c.le(b))
//     )]
//     fn maximal_idemp(a: Self) { }
// }

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
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(
        a.op(b).and_then_logic(|x:Self| x.op(c)) ==
        b.op(c).and_then_logic(|x:Self| a.op(x))
    )]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(
        (forall<b: Self> ! (b.le(a) && b.idemp())) ||
        (exists<b: Self> b.le(a) && b.idemp() &&
           forall<c: Self> c.le(a) && c.idemp() ==> c.le(b))
    )]
    fn maximal_idemp(a: Self) { }
}

// impl<T> RA for Option<T>
//     where T: RA
// {
//     #[logic]
//     #[open]
//     fn op(self, other: Self) -> Option<Self> { pearlite!{
//         match (self, other) {
//             (None, _) => Some(other),
//             (_, None) => Some(self),
//             (Some(x), Some(y)) => x.op(y).and_then_logic(|x| Some(Some(x))),
//         }
//     }}

//     #[logic]
//     #[open]
//     #[ensures(result == (self == other || exists<c: Self> self.op(c) == Some(other)))]
//     fn le(self, other: Self) -> bool {
//         match (self, other) {
//             (None, _) => true,
//             (_, None) => false,
//             (Some(x), Some(y)) => {
//                 x.le(y)
//             }
//         }
//     }

//     #[logic]
//     #[open]
//     #[ensures(result == (self.op(self) == Some(self)))]
//     fn idemp(self) -> bool {
//         match self {
//             None => true,
//             Some(x) => x.idemp(),
//         }
//     }

//     #[logic]
//     #[open(self)]
//     #[ensures(a.op(b) == b.op(a))]
//     fn commutative(a: Self, b: Self) {
//         // TODO: better syntax?
//         let _ = <T as RA>::commutative;
//     }

//     #[logic]
//     #[open(self)]
//     #[ensures(
//         a.op(b).and_then_logic(|x:Self| x.op(c)) ==
//         b.op(c).and_then_logic(|x:Self| a.op(x))
//     )]
//     fn associative(a: Self, b: Self, c: Self) { pearlite!{
//         match (a, b, c) {
//             (None, _, _) => {},
//             (_, None, _) => {},
//             (_, _, None) => {},
//             (Some(aa), Some(bb), Some(cc)) => {
//                 <T as RA>::associative(aa, bb, cc)
//             }
//         }
//     }}

//     #[logic]
//     #[open(self)]
//     #[ensures(
//         (forall<b: Self> ! (b.le(a) && b.idemp())) ||
//         (exists<b: Self> b.le(a) && b.idemp() &&
//            forall<c: Self> c.le(a) && c.idemp() ==> c.le(b))
//     )]
//     fn maximal_idemp(a: Self) {
//         let _ = <T as RA>::maximal_idemp;
//     }
// }

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
