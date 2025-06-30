use crate::{
    logic::ra::{
        UnitRA,
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

impl<T: UnitRA> ViewRel for AuthViewRel<T> {
    type Auth = T;
    type Frag = T;

    #[logic]
    #[open]
    fn rel(a: Option<T>, f: T) -> bool {
        match a {
            Some(a) => f.incl(a),
            None => true,
        }
    }

    #[law]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Option<T>, f1: T, f2: T) {}

    #[law]
    #[ensures(Self::rel(None, f))]
    fn rel_none(a: Option<T>, f: T) {}

    #[law]
    #[ensures(Self::rel(a, T::unit()))]
    fn rel_unit(a: Option<T>) {}
}
