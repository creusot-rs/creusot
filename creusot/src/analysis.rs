use creusot_rustc::{
    index::bit_set::BitSet,
    middle::mir::visit::{
        MutatingUseContext, NonMutatingUseContext, NonUseContext, PlaceContext, Visitor,
    },
    smir::mir::{self, Local, Location},
};

pub(crate) mod uninit_locals;
pub(crate) mod variance;

pub struct NeverLive(BitSet<Local>);

/// Count locals which are never used and therefore can never be considered live.
/// We use this to account for function arguments which are never live when calculating
/// when to drop them.
impl NeverLive {
    pub(crate) fn for_body(body: &mir::Body) -> BitSet<Local> {
        let mut ever_live = NeverLive(BitSet::new_filled(body.local_decls.len()));
        ever_live.visit_body(body);
        ever_live.0
    }
}

impl<'tcx> Visitor<'tcx> for NeverLive {
    fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, location: Location) {
        self.visit_projection(place.as_ref(), context, location);

        let mir::Place { projection, local } = *place;

        match categorize(context) {
            // Treat derefs as a use of the base local. `*p = 4` is not a def of `p` but a use.
            Some(_) if place.is_indirect() => {
                self.0.remove(local);
            }

            Some(DefUse::Def) if projection.is_empty() => {}
            Some(DefUse::Use) => {
                self.0.remove(local);
            }
            _ => {}
        }
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        match categorize(context) {
            Some(DefUse::Def) => {}
            Some(DefUse::Use) => {
                self.0.remove(local);
            }
            _ => {}
        }
    }
}

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

#[derive(Eq, PartialEq, Clone)]
pub enum DefUse {
    Def,
    Use,
    Drop,
}

pub(crate) fn categorize(context: PlaceContext) -> Option<DefUse> {
    match context {
        ///////////////////////////////////////////////////////////////////////////
        // DEFS

        PlaceContext::MutatingUse(MutatingUseContext::Store) |

        // We let Call define the result in both the success and
        // unwind cases. This is not really correct, however it
        // does not seem to be observable due to the way that we
        // generate MIR. To do things properly, we would apply
        // the def in call only to the input from the success
        // path and not the unwind path. -nmatsakis
        PlaceContext::MutatingUse(MutatingUseContext::Call) |
        // PlaceContext::MutatingUse(MutatingUseContext::LlvmAsmOutput) |
        PlaceContext::MutatingUse(MutatingUseContext::AsmOutput) |
        PlaceContext::MutatingUse(MutatingUseContext::Yield) |

        // Storage live and storage dead aren't proper defines, but we can ignore
        // values that come before them.
        PlaceContext::NonUse(NonUseContext::StorageLive) |
        PlaceContext::NonUse(NonUseContext::StorageDead) => Some(DefUse::Def),

        ///////////////////////////////////////////////////////////////////////////
        // REGULAR USES
        //
        // These are uses that occur *outside* of a drop. For the
        // purposes of NLL, these are special in that **all** the
        // lifetimes appearing in the variable must be live for each regular use.

        PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection) |
        PlaceContext::MutatingUse(MutatingUseContext::Projection) |

        // Borrows only consider their local used at the point of the borrow.
        // This won't affect the results since we use this analysis for generators
        // and we only care about the result at suspension points. Borrows cannot
        // cross suspension points so this behavior is unproblematic.
        PlaceContext::MutatingUse(MutatingUseContext::Borrow) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::SharedBorrow) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::ShallowBorrow) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::UniqueBorrow) |

        PlaceContext::MutatingUse(MutatingUseContext::AddressOf) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::AddressOf) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::Inspect) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::Copy) |
        PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) |
        PlaceContext::NonUse(NonUseContext::AscribeUserTy) |
        PlaceContext::MutatingUse(MutatingUseContext::Retag) =>
            Some(DefUse::Use),

        ///////////////////////////////////////////////////////////////////////////
        // DROP USES
        //
        // These are uses that occur in a DROP (a MIR drop, not a
        // call to `std::mem::drop()`). For the purposes of NLL,
        // uses in drop are special because `#[may_dangle]`
        // attributes can affect whether lifetimes must be live.

        PlaceContext::MutatingUse(MutatingUseContext::Drop) =>
            Some(DefUse::Drop),

        // Debug info is neither def nor use.
        PlaceContext::NonUse(NonUseContext::VarDebugInfo) => None,

        PlaceContext::MutatingUse(MutatingUseContext::Deinit | MutatingUseContext::SetDiscriminant) => {
            unreachable!("These statements are not allowed in this MIR phase")
        }
    }
}
