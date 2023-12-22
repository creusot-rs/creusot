use rustc_ast::Mutability;
use rustc_middle::{
    mir::{
        Body, BorrowKind, Location, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
    },
    ty::{List, TyCtxt},
};
use rustc_mir_dataflow::{
    impls::MaybeLiveLocals, Analysis, AnalysisDomain, Results, ResultsVisitor,
};

struct Visitor<'mir, 'tcx> {
    patch: Vec<(Location, Statement<'tcx>)>,
    mir: &'mir Body<'tcx>,
}

impl<'mir, 'tcx> ResultsVisitor<'mir, 'tcx, Results<'tcx, MaybeLiveLocals>>
    for Visitor<'mir, 'tcx>
{
    type FlowState = <MaybeLiveLocals as AnalysisDomain<'tcx>>::Domain;
    fn visit_statement_before_primary_effect(
        &mut self,
        _: &Results<'tcx, MaybeLiveLocals>,
        state: &Self::FlowState,
        statement: &'mir Statement<'tcx>,
        location: Location,
    ) {
        match &statement.kind {
            StatementKind::Assign(box (place, Rvalue::Ref(_, BorrowKind::Mut { .. }, rplace)))
                if rplace.projection.iter().eq([PlaceElem::Deref])
                    && !state.contains(rplace.local)
                    && self.mir.local_decls[rplace.local].ty.ref_mutability() // don't convert raw-pointers
                        == Some(Mutability::Mut) =>
            {
                // place = &mut * local => place = move local
                let new_rplace = Place { local: rplace.local, projection: List::empty() };
                let new_rplace = Rvalue::Use(Operand::Move(new_rplace));
                let kind = StatementKind::Assign(Box::new((*place, new_rplace)));
                let source_info = statement.source_info.clone();
                self.patch.push((location, Statement { kind, source_info }))
            }
            _ => {}
        }
    }
}

/// Cleans up unnecessary reborrows
/// x = &mut * y => x = move y
/// when y is dead afterwards
pub(crate) fn remove_mir_reborrows<'tcx>(tcx: TyCtxt<'tcx>, mir: &mut Body<'tcx>) {
    let mut vistor = Visitor { patch: Vec::new(), mir };
    MaybeLiveLocals
        .into_engine(tcx, mir)
        .iterate_to_fixpoint()
        .visit_reachable_with(mir, &mut vistor);
    for (loc, statement) in vistor.patch {
        mir.basic_blocks.as_mut()[loc.block].statements[loc.statement_index] = statement;
    }
}
