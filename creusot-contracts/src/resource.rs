#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::{Ghost, Snapshot, *};
use crate::logic::Set;
use crate::logic::{ra, ra::RA};
use ::std::marker::PhantomData;

// TODO: move to a separate file
use crate::pcell::Id;

// TODO: explicit fields ? but, could the user mutate them?
// TODO: other definition?
pub struct Resource<R>(PhantomData<R>);

impl<R: RA> Resource<R> {
    #[logic]
    #[trusted]
    pub fn id(self) -> Id {
        dead
    }

    #[logic]
    #[trusted]
    pub fn val(self) -> R {
        dead
    }

    #[trusted]
    #[requires(r.valid())]
    #[ensures(result.val() == r)]
    pub fn alloc(r: R) -> Ghost<Self> { Ghost::conjure() }

    // NOTE: couldn't we somehow make the logical model of Snapshot<T> to be T?
    // (so we could get rid of these extra * in specs)

    #[trusted]
    #[requires(self.val() == a.op(*b))]
    #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
    #[ensures(result.0.val() == *a)]
    #[ensures(result.1.val() == *b)]
    pub fn split(self, a: Snapshot<R>, b: Snapshot<R>) -> (Self, Self) { panic!() }

    #[trusted]
    #[requires(self.id() == other.id())]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self).val() == self.val().op(other.val()))]
    pub fn join(&mut self, other: Self) { panic!() }

    // splits, then joins back at resolution
    #[trusted]
    #[requires(self.val() == a.op(*b))]
    #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
    #[ensures(result.0.val() == *a)]
    #[ensures(result.1.val() == *b)]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self).val() == (^result.0).val().op((^result.1).val()))]
    pub fn split_mut<'a>(&'a mut self, a: Snapshot<R>, b: Snapshot<R>) ->
        (&'a mut Self, &'a mut Self)
    {
        panic!()
    }

    #[trusted]
    #[ensures(self.val().valid())]
    pub fn valid(&self) { panic!() }

    #[trusted]
    #[requires(target.incl(self.val()))]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self).val() == *target)]
    pub fn weaken(&mut self, target: Snapshot<R>) { panic!() }

    #[trusted]
    #[requires(ra::update(self.val(), *target))]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self).val() == *target)]
    pub fn update(&mut self, target: Snapshot<R>) { panic!() }

    #[trusted]
    #[requires(ra::update_nondet(self.val(), *target_s))]
    #[ensures((^self).id() == self.id())]
    #[ensures(target_s.contains((^self).val()))]
    pub fn update_nondet(&mut self, target_s: Snapshot<Set<R>>) { panic!() }
}
