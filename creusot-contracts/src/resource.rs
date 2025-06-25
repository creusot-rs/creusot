pub mod fmap_view;

#[cfg(creusot)]
use crate::std::option::OptionExt as _;
use crate::{
    Ghost, Snapshot,
    logic::{Id, Set, ra::RA},
    *,
};
use ::std::marker::PhantomData;

/// A ghost wrapper around a [resource algebra](RA).
///
/// This structure is meant to be manipulated in [`ghost`](mod@ghost) code.
///
/// The usual usage is this:
/// - [Create](Self::alloc) some ghost resource
/// - [Split](Self::split) it into multiple parts, some of which may be [duplicable](RA::idemp)
/// - [Join](Self::join) these parts later. By exploiting validity of the combination, this allows
///   one to learn information about one part from the other.
///
/// # Example
///
/// ```rust
/// use creusot_contracts::{*, resource::Resource, logic::ra::Ag};
/// let mut res: Ghost<Resource<Ag<Int>>> = Resource::alloc(snapshot!(Ag(1)));
///
/// ghost! {
///     let part = res.split_off(snapshot!(Ag(1)), snapshot!(Ag(1)));
///     // Pass `part` around, forget what it contained...
///     let _ = res.join_shared(&part);
///     // And now we remember: the only way this works is if `part` contained `1`!
///     proof_assert!(part@ == Ag(1));
/// };
/// ```
#[trusted]
pub struct Resource<R>(PhantomData<R>);

impl<R: RA> View for Resource<R> {
    type ViewTy = R;
    #[logic]
    #[open]
    fn view(self) -> R {
        self.val()
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

    /// Get the id for this resource.
    ///
    /// This is the same as [`Self::id`], but for ghost code.
    #[pure]
    #[trusted]
    #[ensures(result == self.id())]
    pub fn id_ghost(&self) -> Id {
        panic!("ghost code only")
    }

    /// Get the RA contained in this resource.
    #[logic]
    #[trusted]
    pub fn val(self) -> R {
        dead
    }

    /// Create a new resource
    ///
    /// # Corresponding reasoning
    ///
    /// `⊢ |=> ∃γ, Own(value, γ)`
    #[trusted]
    #[pure]
    #[ensures(result@ == *r)]
    pub fn alloc(r: Snapshot<R>) -> Ghost<Self> {
        Ghost::conjure()
    }

    /// Dummy resource.
    /// This funciton is unsound, because there does not necessarilly exist
    /// a value of the RA that does not carry any ownership.
    ///
    /// However, thanks to this, we can prove some of the functions bellow, that would be
    /// otherwise axiomatized. These proofs are morally trusted, but being to prove them is
    /// a good measure against stupid mistakes in their specifications.
    #[trusted]
    #[pure]
    fn dummy() -> Self {
        Self(PhantomData)
    }

    /// Duplicate a resource if it is idempotent.
    #[trusted]
    #[requires(self@.idemp())]
    #[ensures(result == *self)]
    #[pure]
    #[allow(clippy::should_implement_trait)]
    pub fn clone(&self) -> Self {
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
    #[pure]
    #[requires(Some(self@) == a.op(*b))]
    #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
    #[ensures(result.0@ == *a)]
    #[ensures(result.1@ == *b)]
    pub fn split(self, a: Snapshot<R>, b: Snapshot<R>) -> (Self, Self) {
        panic!("ghost code only")
    }

    /// Split a resource into two, and join it again once the mutable borrows are dropped.
    #[trusted]
    #[pure]
    #[requires(Some(self@) == a.op(*b))]
    #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
    #[ensures(result.0@ == *a)]
    #[ensures(result.1@ == *b)]
    #[ensures((^result.0).id() == self.id() && (^result.1).id() == self.id() ==>
        (^self).id() == self.id() &&
        Some((^self)@) == (^result.0)@.op((^result.1)@))]
    pub fn split_mut(&mut self, a: Snapshot<R>, b: Snapshot<R>) -> (&mut Self, &mut Self) {
        panic!("ghost code only")
    }

    /// Remove `b` from `self` and return it, leaving `a` inside `self`.
    #[pure]
    #[requires(Some(self@) == a.op(*b))]
    #[ensures((^self).id() == self.id())]
    #[ensures(result.id() == self.id())]
    #[ensures((^self)@ == *a)]
    #[ensures(result@ == *b)]
    pub fn split_off(&mut self, a: Snapshot<R>, b: Snapshot<R>) -> Self {
        let this = std::mem::replace(self, Self::dummy());
        let (a, b) = this.split(a, b);
        let _ = std::mem::replace(self, a);
        b
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
    #[ensures(Some(result@) == self@.op(other@))]
    pub fn join(self, other: Self) -> Self {
        panic!("ghost code only")
    }

    /// Same as [`Self::join`], but put the result into `self`.
    #[pure]
    #[requires(self.id() == other.id())]
    #[ensures((^self).id() == self.id())]
    #[ensures(Some((^self)@) == self@.op(other@))]
    pub fn join_mut(&mut self, other: Self) {
        let this = std::mem::replace(self, Self::dummy());
        let this = this.join(other);
        let _ = std::mem::replace(self, this);
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
    #[ensures(self@.incl_eq(result@) && other@.incl_eq(result@))]
    pub fn join_shared<'a>(&'a self, other: &'a Self) -> &'a Self {
        panic!("ghost code only")
    }

    /// Transforms `self` into `target`, given that `target` is included in `self`.
    #[pure]
    #[requires(target.incl(self@))]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self)@ == *target)]
    pub fn weaken(&mut self, target: Snapshot<R>) {
        let this = std::mem::replace(self, Self::dummy());
        let factor = snapshot!(this@.factor(*target).unwrap_logic());
        let (this, _) = this.split(target, factor);
        let _ = std::mem::replace(self, this);
    }

    /// Transform `self` into `target`.
    ///
    /// # Corresponding reasoning
    ///
    /// `⌜a ⇝ b⌝ ∧ Own(a, γ) ⊢ Own(b, γ)`
    #[trusted]
    #[pure]
    #[requires(self@.update(*target))]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self)@ == *target)]
    pub fn update(&mut self, target: Snapshot<R>) {
        panic!("ghost code only")
    }

    /// Validate the composition of `self` and `other`.
    #[trusted]
    #[pure]
    #[requires(self.id() == other.id())]
    #[ensures(^self == *self)]
    #[ensures(self@.op(other@) != None)]
    pub fn valid_shared(&mut self, other: &Self) {}

    /// Transform `self` into an element in `target`, nondeterministically.
    ///
    /// # Corresponding reasoning
    ///
    /// `⌜a ⇝ B⌝ ∧ Own(a, γ) ⊢ ∃b∈B, Own(b, γ)`
    #[trusted]
    #[pure]
    #[requires(self@.update_nondet(*target_s))]
    #[ensures((^self).id() == self.id())]
    #[ensures(target_s.contains((^self)@))]
    pub fn update_nondet(&mut self, target_s: Snapshot<Set<R>>) {
        panic!("ghost code only")
    }
}
