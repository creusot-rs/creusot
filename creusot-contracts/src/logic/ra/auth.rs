use crate::{
    logic::ra::{
        RA,
        view::{View, ViewRel},
    },
    *,
};

/// The 'authority' Resource Algebra.
///
/// This is a specialisation of [`View`], where:
/// - both [`Auth`](ViewRel::Auth) and [`Frag`](ViewRel::Frag) are the same type
/// - the relation between the two is specified by [`AuthViewRel`]: it asserts that
///   `Frag` must always be included in `Auth`
pub type Auth<T> = View<AuthViewRel<T>>;

/// The relation that specifies [`Auth`].
pub struct AuthViewRel<T>(T);

impl<T> ViewRel for AuthViewRel<T>
where
    T: RA,
{
    type Auth = T;
    type Frag = T;

    #[logic]
    #[open]
    fn rel(a: Self::Auth, f: Self::Frag) -> bool {
        f.incl(a) != None && a.valid()
    }

    #[law]
    #[open(self)]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1) != None)]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Self::Auth, f1: Self::Frag, f2: Self::Frag) {}
}
