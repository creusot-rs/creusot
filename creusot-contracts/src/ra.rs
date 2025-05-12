use crate::*;

#[allow(unused_variables)]

pub trait RA: Sized {
    #[logic]
    fn op(self, other: Self) -> Self;

    #[logic]
    fn valid(self) -> bool;

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

    // Derived notions and properties: `incl`, `idemp`.
    // Allow the implementor to give a custom definition, that is possibly
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

    // TODO: prédicat fupd
}

#[logic]
#[open(self)]
#[requires(a.incl(b) && b.incl(c))]
#[ensures(a.incl(c))]
pub fn incl_transitive<T: RA>(a: T, b: T, c: T) { }

//////////////////////////////////////////

pub enum Excl<T> {
    Excl(T),
    ExclBot,
}

#[allow(unused_imports)]
use Excl::*;

impl<T> RA for Excl<T>
{
    #[logic]
    #[open]
    fn op(self, _other: Self) -> Self {
        ExclBot
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Excl(_) => true,
            ExclBot => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        other == ExclBot
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        self == ExclBot
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {}

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) { }
}

pub enum Ag<T> {
    Ag(T),
    AgBot,
}

#[allow(unused_imports)]
use Ag::*;

impl<T> RA for Ag<T>
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (Ag(x), Ag(y)) => {
                if x == y {
                    Ag(x)
                } else {
                    AgBot
                }
            },
            (_, _) =>
                AgBot,
        }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Ag(_) => true,
            AgBot => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        true
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        match (self, other) {
            (Ag(x), Ag(y)) => x == y,
            (_, AgBot) => true,
            (_, Ag(_)) => false,
        }
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {}

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) { }
}

impl<T, U> RA for (T, U)
    where T: RA, U: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        (self.0.op(other.0), self.1.op(other.1))
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        self.0.valid() && self.1.valid()
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        // TODO: check if still necessary
        if self.0.incl(other.0) && self.1.incl(other.1) {
            proof_assert!(exists<c0: T, c1: U>
              self.0.op(c0) == other.0 &&
              self.1.op(c1) == other.1 &&
              self.op((c0, c1)) == other
            )
        }
        self.0.incl(other.0) && self.1.incl(other.1)
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        self.0.idemp() && self.1.idemp()
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        self.0.valid_op(b.0);
        self.1.valid_op(b.1);
    }

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) {
        self.0.maximal_idemp();
        self.1.maximal_idemp();
    }
}

pub enum Sum<T, U> {
    Left(T),
    Right(U),
    SumBot,
}

#[allow(unused_imports)]
use Sum::*;

impl<T, U> RA for Sum<T, U>
    where T: RA, U: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (Left(x), Left(y)) => Left(x.op(y)),
            (Right(x), Right(y)) => Right(x.op(y)),
            (_, _) => SumBot,
        }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Left(x) => x.valid(),
            Right(x) => x.valid(),
            SumBot => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        match (self, other) {
            (Left(x), Left(y)) => x.incl(y),
            (Right(x), Right(y)) => x.incl(y),
            (_, SumBot) => true,
            (_, _) => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        match self {
            Left(x) => x.idemp(),
            Right(x) => x.idemp(),
            SumBot => true,
        }
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        let _ = <T as RA>::valid_op;
        let _ = <U as RA>::valid_op;
    }

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) {
        match self {
            Left(x) => x.maximal_idemp(),
            Right(x) => x.maximal_idemp(),
            SumBot => (),
        }
    }
}

impl<T> RA for Option<T>
    where T: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (None, _) => other,
            (_, None) => self,
            (Some(x), Some(y)) => Some(x.op(y)),
        }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Some(x) => x.valid(),
            None => true,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        match (self, other) {
            (None, _) => true,
            (_, None) => false,
            (Some(x), Some(y)) => {
                x == y || x.incl(y)
            }
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
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
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
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
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        let _ = <T as RA>::valid_op;
    }

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) { pearlite!{
        match self {
            None => (),
            Some(x) => {
                x.maximal_idemp();
                if forall<y: T> ! (y.incl(x) && y.idemp()) {
                    // pick None, show the right-hand side of the postcondition
                    proof_assert!(None.incl(self) && None::<T>.idemp());
                    proof_assert!(forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(None));
                } else {
                    // pick Some(y)
                    proof_assert!(exists<y: T> y.incl(x) && y.idemp() &&
                      Some(y).incl(self) && Some(y).idemp() &&
                      (forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(Some(y)))
                    );
                }
            }
        }
    }}
}

pub trait ViewRel {
    type Auth;
    type Frac: RA;

    #[logic]
    fn rel(a: Self::Auth, f: Self::Frac) -> bool;

    #[law]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Self::Auth, f1: Self::Frac, f2: Self::Frac);
}

// NOTE: we could add (discardable) fractions for the auth part
#[allow(dead_code)]
pub struct View<R> where R: ViewRel
{
    // TODO: should the fields be priv?
    pub auth: Option<Excl<R::Auth>>,
    pub frac: Option<R::Frac>,
}

impl<R> View<R> where R: ViewRel {
    #[logic]
    #[open]
    pub fn mkauth(a: R::Auth) -> Self {
        Self { auth: Some(Excl(a)), frac: None }
    }

    #[logic]
    #[open]
    pub fn mkfrac(f: R::Frac) -> Self {
        Self { auth: None, frac: Some(f) }
    }
}

impl<R> RA for View<R>
where R: ViewRel
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        let (auth, frac) = (self.auth, self.frac).op((other.auth, other.frac));
        Self { auth, frac }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool { pearlite!{
        match self {
            Self { auth: Some(Excl(a)), frac: Some(f) } => f.valid() && R::rel(a, f),
            // TODO: why is this condition necessary?
            Self { auth: None, frac: Some(f) } => f.valid() && exists<a: R::Auth> R::rel(a, f),
            Self { auth: Some(Excl(_)), frac: None } => true,
            Self { auth: None, frac: None } => true,
            Self { auth: Some(ExclBot), frac: _ } => false,
        }
    }}

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        (self.auth, self.frac).incl((other.auth, other.frac))
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        (self.auth, self.frac).idemp()
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        let _ = <R::Frac as RA>::valid_op;
    }

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) {
        self.auth.maximal_idemp();
        self.frac.maximal_idemp();
    }
}

pub struct AuthViewRel<T>(T);

impl<T> ViewRel for AuthViewRel<T>
where T: RA
{
    type Auth = T;
    type Frac = T;

    #[logic]
    #[open]
    fn rel(a: Self::Auth, f: Self::Frac) -> bool {
        f.incl(a) && a.valid()
    }

    #[law]
    #[open(self)]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Self::Auth, f1: Self::Frac, f2: Self::Frac) {}
}

pub struct Auth<T: RA>(pub View<AuthViewRel<T>>);

impl<T> Auth<T> where T: RA {
    #[logic]
    pub fn mkauth(x: T) -> Self {
        Auth(View::mkauth(x))
    }

    #[logic]
    pub fn mkfrac(x: T) -> Self {
        Auth(View::mkfrac(x))
    }
}

// TODO: open vs open(self) for RA impls? abstraction patterns?

impl<T> RA for Auth<T>
    where T: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        Auth(self.0.op(other.0))
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        self.0.valid()
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) {}

    // TODO: should this be a #[law]?
    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        self.0.valid_op(b.0)
    }

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) {
        self.0.maximal_idemp();
    }

    #[logic]
    #[open]
    #[ensures(result == exists<c: Self> self.op(c) == other)]
    fn incl(self, other: Self) -> bool {
        self.0.incl(other.0)
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        self.0.idemp()
    }
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
//     #[ensures(result == (self.op(self) == self))]
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
