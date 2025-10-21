#[cfg(creusot)]
use crate::logic::such_that;
use crate::{
    logic::{Mapping, ra::RA},
    prelude::*,
};

pub trait Update<R: RA> {
    type Choice;

    #[logic]
    fn premise(self, from: R) -> bool;

    #[logic]
    #[requires(self.premise(from))]
    fn update(self, from: R, ch: Self::Choice) -> R;

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: R, frame: R) -> Self::Choice;
}

impl<R: RA> Update<R> for Snapshot<R> {
    type Choice = ();

    #[logic(open)]
    fn premise(self, from: R) -> bool {
        pearlite! {
            forall<y: R> from.op(y) != None ==> self.op(y) != None
        }
    }

    #[logic(open)]
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

impl<R: RA, Choice> Update<R> for Snapshot<Mapping<Choice, R>> {
    type Choice = Choice;

    #[logic(open)]
    fn premise(self, from: R) -> bool {
        pearlite! {
            forall<y: R> from.op(y) != None ==>
                exists<ch: Choice> self[ch].op(y) != None
        }
    }

    #[logic(open)]
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

pub trait LocalUpdate<R: RA>: Sized {
    #[logic]
    fn premise(self, from_auth: R, from_frag: R) -> bool;

    #[logic]
    fn update(self, from_auth: R, from_frag: R) -> (R, R);

    #[logic]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(self, from_auth: R, from_frag: R, frame: Option<R>);
}

impl<R: RA> LocalUpdate<R> for Snapshot<(R, R)> {
    #[logic(open)]
    fn premise(self, from_auth: R, from_frag: R) -> bool {
        pearlite! {
            forall<f: Option<R>>
                Some(from_frag).op(f) == Some(Some(from_auth)) ==>
                Some(self.1).op(f) == Some(Some(self.0))
        }
    }

    #[logic(open)]
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
