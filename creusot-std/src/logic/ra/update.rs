#[cfg(creusot)]
use crate::logic::such_that;
use crate::{
    logic::{Mapping, ra::RA},
    prelude::*,
};

/// Perform an update on a resource.
///
/// This is used by [`Resource::update`](crate::ghost::resource::Resource::update)
/// to specify how to update a resource.
pub trait Update<R: RA> {
    /// If the update is non-deterministic, it will pick a _choice_ of this type
    /// for the update.
    type Choice;

    /// The premise of the update.
    ///
    /// This must be true for the resource before applying the update.
    #[logic]
    fn premise(self, from: R) -> bool;

    /// The actual update performed.
    ///
    /// The content of the resource before the update is `from`. The update will
    /// also choose some element `ch` of `Choice` to make the update with. The
    /// return value will be the content of the resource after the update.
    #[logic]
    #[requires(self.premise(from))]
    fn update(self, from: R, ch: Self::Choice) -> R;

    /// Frame preservation.
    ///
    /// This is a lemma that must be proven by implementors to ensure that the
    /// update is consistent.
    ///
    /// It states that if we were to apply that update, the resulting resource
    /// would have _more_ valid compositions that what we started with, whatever
    /// `Choice` we made.
    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: R, frame: R) -> Self::Choice;
}

/// Apply a 'raw' update.
///
/// This changes the state of the resource from one value to another. The
/// premise of this change is that no existing composition with the resource
/// is invalidated.
impl<R: RA> Update<R> for Snapshot<R> {
    type Choice = ();

    #[logic(open, inline)]
    fn premise(self, from: R) -> bool {
        pearlite! {
            forall<y: R> from.op(y) != None ==> self.op(y) != None
        }
    }

    #[logic(open, inline)]
    #[requires(self.premise(from))]
    fn update(self, from: R, _: ()) -> R {
        *self
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: R, frame: R) {}
}

/// Apply a 'raw' non-deterministic update.
///
/// This changes the state of the resource to _one_ of the values of the
/// mapping, non-deterministically.
impl<R: RA, Choice> Update<R> for Snapshot<Mapping<Choice, R>> {
    type Choice = Choice;

    #[logic(open, inline)]
    fn premise(self, from: R) -> bool {
        pearlite! {
            forall<y: R> from.op(y) != None ==>
                exists<ch: Choice> self[ch].op(y) != None
        }
    }

    #[logic(open, inline)]
    #[requires(self.premise(from))]
    fn update(self, from: R, ch: Choice) -> R {
        self[ch]
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: R, frame: R) -> Choice {
        such_that(|ch| self.update(from, ch).op(frame) != None)
    }
}

/// Apply no update.
impl<R: RA> Update<R> for () {
    type Choice = ();

    #[logic(open, inline)]
    fn premise(self, _: R) -> bool {
        true
    }

    #[logic(open, inline)]
    fn update(self, from: R, _: ()) -> R {
        from
    }

    #[logic]
    #[requires(from.op(frame) != None)]
    #[ensures(from.op(frame) != None)]
    fn frame_preserving(self, from: R, frame: R) {}
}

/// Perform an update on an authority/fragment pair.
///
/// This is similar to [`Update`], but is instead used by
/// [`Authority::update`](crate::ghost::resource::Authority::update) to
/// simultaneously change the value of an authority/fragment pair.
///
/// Note that contrary to [`Update`], this has to be deterministic.
pub trait LocalUpdate<R: RA>: Sized {
    /// The premise of the update.
    ///
    /// This must be true for the authority and the fragment _before_ applying
    /// the update.
    #[logic]
    fn premise(self, from_auth: R, from_frag: R) -> bool;

    /// The update performed.
    ///
    /// This describe how to change the authority/fragment pair.
    #[logic]
    fn update(self, from_auth: R, from_frag: R) -> (R, R);

    /// Frame preservation.
    ///
    /// This is a lemma that must be proven by implementors to ensure that the
    /// update is consistent.
    ///
    /// It states that the 'missing piece' of the authority from the fragment is
    /// still the same after the update.
    #[logic]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(self, from_auth: R, from_frag: R, frame: Option<R>);
}

/// Apply a 'raw' local update.
///
/// This will update the value of the authority/fragment to the provided pair.
impl<R: RA> LocalUpdate<R> for Snapshot<(R, R)> {
    #[logic(open, inline)]
    fn premise(self, from_auth: R, from_frag: R) -> bool {
        pearlite! {
            forall<f: Option<R>>
                Some(from_frag).op(f) == Some(Some(from_auth)) ==>
                Some(self.1).op(f) == Some(Some(self.0))
        }
    }

    #[logic(open, inline)]
    fn update(self, _: R, _: R) -> (R, R) {
        *self
    }

    #[logic]
    #[allow(unused)]
    #[requires(LocalUpdate::premise(self, from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = LocalUpdate::update(self, from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(self, from_auth: R, from_frag: R, frame: Option<R>) {}
}

/// Apply no update.
impl<R: RA> LocalUpdate<R> for () {
    #[logic(open, inline)]
    fn premise(self, _: R, _: R) -> bool {
        true
    }

    #[logic(open, inline)]
    fn update(self, from_auth: R, from_frag: R) -> (R, R) {
        (from_auth, from_frag)
    }

    #[logic]
    #[requires(Some(frag).op(frame) == Some(Some(auth)))]
    #[ensures(Some(frag).op(frame) == Some(Some(auth)))]
    fn frame_preserving(self, auth: R, frag: R, frame: Option<R>) {}
}
