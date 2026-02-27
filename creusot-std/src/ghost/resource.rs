//! Resource algebras
//!
//! See [`Resource`].

mod auth;
pub use auth::{Authority, Fragment};

// We use a nested module that we re-export, to make sure that the definitions
// are opaque to the fmap_view module
mod m {
    #[cfg(creusot)]
    use crate::logic::such_that;
    use crate::{
        logic::{
            Id, Set,
            ra::{RA, UnitRA, update::Update},
        },
        prelude::*,
    };
    use core::marker::PhantomData;

    /// A ghost wrapper around a [resource algebra](RA).
    ///
    /// This structure is meant to be manipulated in [`ghost`] code.
    ///
    /// The usual usage is this:
    /// - [Create](Self::alloc) some ghost resource
    /// - [Split](Self::split) it into multiple parts.
    ///   This may be used to duplicate the resource if we have `self.op(self) == self`.
    /// - [Join](Self::join) these parts later. By exploiting validity of the combination, this allows
    ///   one to learn information about one part from the other.
    ///
    /// # Example
    ///
    /// ```rust
    /// use creusot_std::{ghost::resource::Resource, logic::ra::agree::Ag, prelude::*};
    /// let mut res: Ghost<Resource<Ag<Int>>> = Resource::alloc(snapshot!(Ag(1)));
    ///
    /// ghost! {
    ///     let part = res.split_off(snapshot!(Ag(1)), snapshot!(Ag(1)));
    ///     // Pass `part` around, forget what it contained...
    ///     let _ = res.join_shared(&part);
    ///     // And now we remember: the only way the above worked is if `part` contained `1`!
    ///     proof_assert!(part@ == Ag(1));
    /// };
    /// ```
    #[opaque]
    pub struct Resource<R>(PhantomData<R>);

    unsafe impl<R> Send for Resource<R> {}

    impl<R: RA> View for Resource<R> {
        type ViewTy = R;
        #[logic(open, inline)]
        fn view(self) -> R {
            self.val()
        }
    }

    #[allow(unused_variables)]
    impl<R: RA> Resource<R> {
        /// Get the id for this resource.
        ///
        /// This prevents mixing resources of different origins.
        #[logic(opaque)]
        pub fn id(self) -> Id {
            dead
        }

        /// Get the id for this resource.
        ///
        /// This is the same as [`Self::id`], but for ghost code.
        #[trusted]
        #[check(ghost)]
        #[ensures(result == self.id())]
        pub fn id_ghost(&self) -> Id {
            panic!("ghost code only")
        }

        /// Get the RA element contained in this resource.
        #[logic(opaque)]
        pub fn val(self) -> R {
            dead
        }

        /// Create a new resource
        ///
        /// # Corresponding reasoning
        ///
        /// `⊢ |=> ∃γ, Own(value, γ)`
        #[trusted]
        #[check(ghost)]
        #[ensures(result@ == *r)]
        pub fn alloc(r: Snapshot<R>) -> Ghost<Self> {
            Ghost::conjure()
        }

        /// Create a unit resource for a given identifier
        #[trusted]
        #[check(ghost)]
        #[ensures(result@ == R::unit() && result.id() == id)]
        pub fn new_unit(id: Id) -> Self
        where
            R: UnitRA,
        {
            panic!("ghost code only")
        }

        /// Dummy resource.
        /// This funciton is unsound, because there does not necessarilly exist
        /// a value of the RA that does not carry any ownership.
        ///
        /// However, thanks to this, we can prove some of the functions bellow, that would be
        /// otherwise axiomatized. These proofs are morally trusted, but being to prove them is
        /// a good measure against stupid mistakes in their specifications.
        #[trusted]
        #[check(ghost)]
        fn dummy() -> Self {
            panic!("ghost code only")
        }

        /// Duplicate the duplicable core of a resource
        #[trusted]
        #[requires(self@.core() != None)]
        #[ensures(result.id() == self.id())]
        #[ensures(Some(result@) == self@.core())]
        #[check(ghost)]
        pub fn core(&self) -> Self {
            panic!("ghost code only")
        }

        /// Split a resource into two parts, described by `a` and `b`.
        ///
        /// See also [`Self::split_mut`] and [`Self::split_off`].
        ///
        /// # Corresponding reasoning
        ///
        /// `⌜a = b ⋅ c⌝ ∧ Own(a, γ) ⊢ Own(b, γ) ∗ Own(c, γ)`
        #[trusted]
        #[check(ghost)]
        #[requires(R::incl_eq_op(*a, *b, self@))]
        #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
        #[ensures(result.0@ == *a)]
        #[ensures(result.1@ == *b)]
        pub fn split(self, a: Snapshot<R>, b: Snapshot<R>) -> (Self, Self) {
            panic!("ghost code only")
        }

        /// Split a resource into two, and join it again once the mutable borrows are dropped.
        #[trusted]
        #[check(ghost)]
        #[requires(R::incl_eq_op(*a, *b, self@))]
        #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
        #[ensures(result.0@ == *a && result.1@ == *b)]
        #[ensures((^result.0).id() == self.id() && (^result.1).id() == self.id() ==>
            (^self).id() == self.id() &&
            Some((^self)@) == (^result.0)@.op((^result.1)@))]
        pub fn split_mut(&mut self, a: Snapshot<R>, b: Snapshot<R>) -> (&mut Self, &mut Self) {
            panic!("ghost code only")
        }

        /// Remove `r` from `self` and return it, leaving `s` in `self`.
        #[check(ghost)]
        #[requires(R::incl_eq_op(*r, *s, self@))]
        #[ensures((^self).id() == self.id() && result.id() == self.id())]
        #[ensures((^self)@ == *s)]
        #[ensures(result@ == *r)]
        pub fn split_off(&mut self, r: Snapshot<R>, s: Snapshot<R>) -> Self {
            let this = core::mem::replace(self, Self::dummy());
            let (r, this) = this.split(r, s);
            let _ = core::mem::replace(self, this);
            r
        }

        /// Join two owned resources together.
        ///
        /// See also [`Self::join_in`] and [`Self::join_shared`].
        ///
        /// # Corresponding reasoning
        ///
        /// `⌜c = a ⋅ b⌝ ∗ Own(a, γ) ∗ Own(b, γ) ⊢ Own(c, γ)`
        #[trusted]
        #[check(ghost)]
        #[requires(self.id() == other.id())]
        #[ensures(result.id() == self.id())]
        #[ensures(Some(result@) == self@.op(other@))]
        pub fn join(self, other: Self) -> Self {
            panic!("ghost code only")
        }

        /// Same as [`Self::join`], but put the result into `self`.
        #[check(ghost)]
        #[requires(self.id() == other.id())]
        #[ensures((^self).id() == self.id())]
        #[ensures(Some((^self)@) == self@.op(other@))]
        pub fn join_in(&mut self, other: Self) {
            let this = core::mem::replace(self, Self::dummy());
            let this = this.join(other);
            let _ = core::mem::replace(self, this);
        }

        /// Join two shared resources together.
        ///
        /// # Corresponding reasoning
        ///
        /// `⌜a ≼ c⌝ ∧ ⌜b ≼ c⌝ ∧ Own(a, γ) ∧ Own(b, γ) ⊢ Own(c, γ)`
        #[trusted]
        #[check(ghost)]
        #[requires(self.id() == other.id())]
        #[ensures(result.id() == self.id())]
        #[ensures(self@.incl_eq(result@) && other@.incl_eq(result@))]
        pub fn join_shared<'a>(&'a self, other: &'a Self) -> &'a Self {
            panic!("ghost code only")
        }

        /// Transforms `self` into `target`, given that `target` is included in `self`.
        #[check(ghost)]
        #[requires(target.incl(self@))]
        #[ensures((^self).id() == self.id())]
        #[ensures((^self)@ == *target)]
        pub fn weaken(&mut self, target: Snapshot<R>) {
            let f = snapshot! {self@.factor(*target).unwrap_logic()};
            self.split_off(f, target);
        }

        /// Validate the composition of `self` and `other`.
        #[trusted]
        #[check(ghost)]
        #[requires(self.id() == other.id())]
        #[ensures(^self == *self)]
        #[ensures(self@.op(other@) != None)]
        pub fn valid_op_lemma(&mut self, other: &Self) {}

        /// This private function axiomatizes updates as they are formalized in Iris.
        #[trusted]
        #[check(ghost)]
        #[requires(forall<f: Option<R>> Some(self@).op(f) != None ==>
                        exists<x: R> target_s.contains(x) && Some(x).op(f) != None)]
        #[ensures((^self).id() == self.id())]
        #[ensures(target_s.contains(*result))]
        #[ensures((^self)@ == *result)]
        fn update_raw(&mut self, target_s: Snapshot<Set<R>>) -> Snapshot<R> {
            panic!("ghost code only")
        }

        /// Perform an update.
        ///
        /// This function will change the content of the resource, according
        /// to `upd`.
        ///
        /// If the update is non-deterministic, this function will return the
        /// _choice_ it made.
        ///
        /// # Corresponding reasoning
        ///
        /// `⌜a ⇝ B⌝ ∧ Own(a, γ) ⊢ ∃b∈B, Own(b, γ)`
        #[check(ghost)]
        #[requires(upd.premise(self@))]
        #[ensures((^self).id() == self.id())]
        #[ensures((^self)@ == upd.update(self@, *result))]
        pub fn update<U: Update<R>>(&mut self, upd: U) -> Snapshot<U::Choice> {
            let v = snapshot!(self@);
            let target_s = snapshot!(Set::from_predicate(|r| exists<ch> upd.update(*v, ch) == r));
            proof_assert!(target_s.contains(upd.update(*v, such_that(|_| true))));
            proof_assert!(
                forall<f: R> v.op(f) != None ==>
                    exists<ch: U::Choice> upd.update(*v, ch).op(f) != None
            );
            let _ = snapshot!(U::frame_preserving);
            let r = self.update_raw(target_s);
            snapshot!(such_that(|ch| upd.update(*v, ch) == *r))
        }
    }

    impl<R: UnitRA> Resource<R> {
        #[check(ghost)]
        #[ensures((^self).id() == self.id() && result.id() == self.id())]
        #[ensures((^self)@ == UnitRA::unit())]
        #[ensures(result@ == self@)]
        pub fn take(&mut self) -> Self {
            let r = snapshot!(self@);
            self.split_off(r, snapshot!(UnitRA::unit()))
        }
    }
}

pub use m::*;
