pub mod gmap;

use crate::{
    Ghost, Snapshot,
    logic::{Set, ra::RA},
    *,
};
#[cfg(creusot)]
use crate::{
    logic::ra,
    // TODO: move to a separate file
    pcell::Id,
};
use ::std::marker::PhantomData;

/// A ghost wrapper around a [resource algebra](RA).
///
/// This structure is meant to be manipulated in [`ghost`](mod@ghost) code. It is
/// guaranteed to always contain a [`valid`](RA::valid) resource.
///
/// The usual usage is this:
/// - [Create](Self::alloc) some ghost resource
/// - [Split](Self::split) it into multiple parts, some of which may be [duplicable](RA::idemp)
/// - [Join](Self::join) these parts later. By the validity invariant, this allows
///   one to learn information about one part from the other.
///
/// # Example
///
/// ```rust
/// use creusot_contracts::{*, logic::ra::{Resource, agree::Ag}};
/// let mut res = Resource::new(snapshot!(Ag::Ag(1)));
///
/// let part = res.split_off(snapshot!(Ag::Ag(1)), snapshot!(Ag::Ag(1)));
/// // Pass `part` around, forget what it contained...
/// let _ = res.join_shared(&part);
/// // And now we remember: the only way this works is if `part` contained `1`!
/// proof_assert!(part@ == Ag::Ag(1));
/// ```
// TODO: explicit fields ? but, could the user mutate them?
// TODO: other definition?
pub struct Resource<R>(PhantomData<R>);

impl<R: RA> View for Resource<R> {
    type ViewTy = R;
    #[logic]
    #[open]
    fn view(self) -> R {
        self.val()
    }
}

impl<R: RA> Invariant for Resource<R> {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        self.val().valid()
    }
}

#[allow(unused_variables)]
impl<R: RA> Resource<R> {
    /// Get the id for this resource.
    ///
    /// This prevents mixing resources of different origins.
    #[logic]
    #[trusted]
    pub fn id(self) -> Id {
        dead
    }

    /// Get the RA contained in this resource.
    #[logic]
    #[trusted]
    pub fn val(self) -> R {
        dead
    }

    /// Create a new resource from a valid value.
    ///
    /// # Corresponding reasoning
    ///
    /// `⌜valid(value)⌝ ⊢ ∃γ, Own(value, γ)`
    #[trusted]
    #[requires(r.valid())]
    #[ensures(result@ == *r)]
    pub fn alloc(r: Snapshot<R>) -> Ghost<Self> {
        Ghost::conjure()
    }

    // NOTE: couldn't we somehow make the logical model of Snapshot<T> to be T?
    // (so we could get rid of these extra * in specs)

    /// Split a resource into two parts, described by `a` and `b`.
    ///
    /// See also [`Self::split_mut`] and [`Self::split_off`].
    ///
    /// # Corresponding reasoning
    ///
    /// `⌜a = b ⋅ c⌝ ∧ Own(a, γ) ⊢ Own(b, γ) ∗ Own(c, γ)`
    #[trusted]
    #[pure]
    #[requires(self@ == a.op(*b))]
    #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
    #[ensures(result.0@ == *a)]
    #[ensures(result.1@ == *b)]
    pub fn split(self, a: Snapshot<R>, b: Snapshot<R>) -> (Self, Self) {
        panic!("ghost code only")
    }

    /// Split a resource into two, and join it again once the mutable borrows are dropped.
    #[trusted]
    #[pure]
    #[requires(self@ == a.op(*b))]
    #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
    #[ensures(result.0@ == *a)]
    #[ensures(result.1@ == *b)]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self)@ == (^result.0)@.op((^result.1)@))]
    pub fn split_mut(&mut self, a: Snapshot<R>, b: Snapshot<R>) -> (&mut Self, &mut Self) {
        panic!("ghost code only")
    }

    /// Remove `b` from `self` and return it, leaving `a` inside `self`.
    #[trusted]
    #[pure]
    #[requires(self@ == a.op(*b))]
    #[ensures((^self).id() == self.id())]
    #[ensures(result.id() == self.id())]
    #[ensures((^self)@ == *a)]
    #[ensures(result@ == *b)]
    pub fn split_off(&mut self, a: Snapshot<R>, b: Snapshot<R>) -> Self {
        panic!("ghost code only")
    }

    /// Join two owned resources together.
    ///
    /// See also [`Self::join_mut`] and [`Self::join_shared`].
    ///
    /// # Corresponding reasoning
    ///
    /// `⌜c = a ⋅ b⌝ ∗ Own(a, γ) ∗ Own(b, γ) ⊢ Own(c, γ)`
    #[trusted]
    #[pure]
    #[requires(self.id() == other.id())]
    #[ensures(result.id() == self.id())]
    #[ensures(result@ == self@.op(other@))]
    pub fn join(self, other: Self) -> Self {
        panic!("ghost code only")
    }

    /// Same as [`Self::join`], but put the result into `self`.
    #[trusted]
    #[pure]
    #[requires(self.id() == other.id())]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self)@ == self@.op(other@))]
    pub fn join_mut(&mut self, other: Self) {
        panic!("ghost code only")
    }

    /// Join two shared resources together.
    ///
    /// # Corresponding reasoning
    ///
    /// `⌜a ≼ c⌝ ∧ ⌜b ≼ c⌝ ∧ Own(a, γ) ∧ Own(b, γ) ⊢ Own(c, γ)`
    #[trusted]
    #[pure]
    #[requires(self.id() == other.id())]
    #[ensures(result.id() == self.id())]
    #[ensures(self@.incl(result@) && other@.incl(result@))]
    pub fn join_shared<'a>(&'a self, other: &'a Self) -> &'a Self {
        panic!("ghost code only")
    }

    #[trusted]
    #[pure]
    #[requires(target.incl(self@))]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self)@ == *target)]
    pub fn weaken(&mut self, target: Snapshot<R>) {
        panic!("ghost code only")
    }

    /// Transform `self` into `target`.
    ///
    /// # Corresponding reasoning
    ///
    /// `⌜a ⇝ b⌝ ∧ Own(a, γ) ⊢ Own(b, γ)`
    #[trusted]
    #[pure]
    #[requires(ra::update(self@, *target))]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self)@ == *target)]
    pub fn update(&mut self, target: Snapshot<R>) {
        panic!("ghost code only")
    }

    /// Transform `self` into an element in `target`, nondeterministically.
    ///
    /// # Corresponding reasoning
    ///
    /// `⌜a ⇝ B⌝ ∧ Own(a, γ) ⊢ ∃b∈B, Own(b, γ)`
    #[trusted]
    #[pure]
    #[requires(ra::update_nondet(self@, *target_s))]
    #[ensures((^self).id() == self.id())]
    #[ensures(target_s.contains((^self)@))]
    pub fn update_nondet(&mut self, target_s: Snapshot<Set<R>>) {
        panic!("ghost code only")
    }
}
