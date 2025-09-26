use ::std::marker::PhantomData;

use crate::{
    logic::ra::{
        RA, UnitRA,
        update::{LocalUpdate, Update},
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
pub struct AuthViewRel<T>(PhantomData<T>);

impl<T: UnitRA> ViewRel for AuthViewRel<T> {
    type Auth = T;
    type Frag = T;

    #[logic(open)]
    fn rel(a: Option<T>, f: T) -> bool {
        match a {
            Some(a) => f.incl(a),
            None => true,
        }
    }

    #[logic(law)]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Option<T>, f1: T, f2: T) {}

    #[logic(law)]
    #[ensures(Self::rel(None, f))]
    fn rel_none(a: Option<T>, f: T) {}

    #[logic(law)]
    #[ensures(Self::rel(a, T::unit()))]
    fn rel_unit(a: Option<T>) {}
}

pub struct AuthUpdate<U>(pub U);

impl<R: UnitRA, U: LocalUpdate<R>> Update<Auth<R>> for AuthUpdate<U> {
    type Choice = ();

    #[logic(open)]
    fn premise(self, from: Auth<R>) -> bool {
        match from.auth() {
            Some(auth) => self.0.premise(auth, from.frag()),
            None => false,
        }
    }

    #[logic(open)]
    #[requires(self.premise(from))]
    #[ensures({
        let (auth, frag) = self.0.update(from.auth().unwrap_logic(), from.frag());
        AuthViewRel::rel(Some(auth), frag)
    })]
    fn update(self, from: Auth<R>, _: ()) -> Auth<R> {
        let (auth, frag) = self.0.update(from.auth().unwrap_logic(), from.frag());
        let _ = U::frame_preserving;
        Auth::new(Some(auth), frag)
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: Auth<R>, frame: Auth<R>) {
        let auth = from.auth().unwrap_logic();
        let x = from.op(frame).unwrap_logic().frag();
        let y = auth.factor(x).unwrap_logic();
        let f = frame.frag().op(y).unwrap_logic();
        self.0.frame_preserving(auth, from.frag(), Some(f));
    }
}
