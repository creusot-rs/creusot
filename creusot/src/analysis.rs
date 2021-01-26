use rustc_index::bit_set::BitSet;
use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{self, Local, Location};

pub struct NeverLive(BitSet<Local>);

impl NeverLive {
    pub fn for_body(body: &mir::Body) -> BitSet<Local> {
        let mut ever_live = NeverLive(BitSet::new_filled(body.local_decls.len()));
        ever_live.visit_body(body);
        ever_live.0
    }
}

impl<'tcx> Visitor<'tcx> for NeverLive {
    fn visit_place(&mut self, place: &mir::Place< 'tcx>, context: PlaceContext, location: Location) {
        let mir::Place { projection, local } = *place;

        self.visit_projection(local, projection, context, location);

        match DefUse::for_place(context) {
            // Treat derefs as a use of the base local. `*p = 4` is not a def of `p` but a use.
            Some(_) if place.is_indirect() => {self.0.remove(local);},

            Some(DefUse::Def) if projection.is_empty() => {},
            Some(DefUse::Use) => {self.0.remove(local); },
            _ => {}
        }
    }

    fn visit_local(&mut self, &local: &Local, context:PlaceContext, _location:Location) {
        match DefUse::for_place(context) {
            Some(DefUse::Def) => {},
            Some(DefUse::Use) => {self.0.remove(local);}
            _ => {}
        }
    }
}

#[derive(Eq, PartialEq, Clone)]
enum DefUse {
    Def,
    Use,
}

impl DefUse {
    fn for_place(context: PlaceContext) -> Option<DefUse> {
        match context {
            PlaceContext::NonUse(_) => None,

            PlaceContext::MutatingUse(MutatingUseContext::Store) => Some(DefUse::Def),

            // `MutatingUseContext::Call` and `MutatingUseContext::Yield` indicate that this is the
            // destination place for a `Call` return or `Yield` resume respectively. Since this is
            // only a `Def` when the function returns successfully, we handle this case separately
            // in `call_return_effect` above.
            PlaceContext::MutatingUse(MutatingUseContext::Call | MutatingUseContext::Yield) => None,

            // All other contexts are uses...
            PlaceContext::MutatingUse(
                MutatingUseContext::AddressOf
                | MutatingUseContext::AsmOutput
                | MutatingUseContext::Borrow
                | MutatingUseContext::Drop
                | MutatingUseContext::Retag,
            )
            | PlaceContext::NonMutatingUse(
                NonMutatingUseContext::AddressOf
                | NonMutatingUseContext::Copy
                | NonMutatingUseContext::Inspect
                | NonMutatingUseContext::Move
                | NonMutatingUseContext::ShallowBorrow
                | NonMutatingUseContext::SharedBorrow
                | NonMutatingUseContext::UniqueBorrow,
            ) => Some(DefUse::Use),

            PlaceContext::MutatingUse(MutatingUseContext::Projection)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection) => {
                unreachable!("A projection could be a def or a use and must be handled separately")
            }
        }
    }
}
