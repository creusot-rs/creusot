use core::marker::PhantomData;

use crate::{
    logic::ra::{
        RA, UnitRA,
        update::{LocalUpdate, Update},
        view::{View, ViewRel},
    },
    prelude::*,
};

/// The 'authority' Resource Algebra.
///
/// This is a specialisation of [`View`], where:
/// - both [`Auth`](ViewRel::Auth) and [`Frag`](ViewRel::Frag) are the same type
/// - the relation between the two is specified by [`AuthViewRel`]: it asserts that
///   `Frag` must always be included in `Auth`
///
/// If this type is directly used as a ghost resource, one should rather use
/// [`crate::ghost::resource::Authority`] or [`crate::ghost::resource::Fragment`], which provides convenient wrappers which the provers prefer.
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

/// Apply an [update](Update) to an [`Auth`] resource, by using a [local
/// update](LocalUpdate) on the authority/fragment.
pub struct AuthUpdate<U>(pub U);

impl<R: UnitRA, U: LocalUpdate<R>> Update<Auth<R>> for AuthUpdate<U> {
    type Choice = ();

    #[logic(open, inline)]
    fn premise(self, from: Auth<R>) -> bool {
        match from.auth() {
            Some(auth) => self.0.premise(auth, from.frag()),
            None => false,
        }
    }

    #[logic]
    #[requires(self.premise(from))]
    #[ensures(result.auth() == Some(self.0.update(from.auth().unwrap_logic(), from.frag()).0))]
    #[ensures(result.frag() == self.0.update(from.auth().unwrap_logic(), from.frag()).1)]
    fn update(self, from: Auth<R>, _: ()) -> Auth<R> {
        let from_auth = from.auth().unwrap_logic();
        let (auth, frag) = self.0.update(from_auth, from.frag());
        self.0.frame_preserving(from_auth, from.frag(), from_auth.factor(from.frag()));
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

/// Add some data to both an authority and a fragment, at the same time.
///
/// Used in `Authority::add_fragment`.
pub(crate) struct AuthIncrease<R>(pub Snapshot<R>);

impl<R: UnitRA> LocalUpdate<R> for AuthIncrease<R> {
    #[logic(open)]
    fn premise(self, from_auth: R, from_frag: R) -> bool {
        from_auth.op(*self.0) != None
            && from_frag.op(*self.0) != None
            && AuthViewRel::rel(Some(from_auth), from_frag)
    }

    #[logic(open)]
    fn update(self, from_auth: R, from_frag: R) -> (R, R) {
        (from_auth.op(*self.0).unwrap_logic(), from_frag.op(*self.0).unwrap_logic())
    }

    #[logic]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(self, from_auth: R, from_frag: R, frame: Option<R>) {}
}
