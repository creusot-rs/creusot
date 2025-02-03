use crate::contracts_items::{is_no_translate, is_snapshot_closure, no_mir};
use indexmap::IndexSet;
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec};
use rustc_middle::{
    mir::{
        visit::{MutVisitor, PlaceContext},
        AggregateKind, BasicBlock, BasicBlockData, Body, Local, Location, Rvalue, SourceInfo,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::TyCtxt,
};

/// Hide non-linear specification code from the borrow checker
///
/// Specifications in Creusot are encoded inside of special closures that are inserted throughout the code.
/// The code inside those closures is meant to be Pearlite and is thus not subject to Rust's borrow checker, however it needs to be able to refer to normal Rust variables.
/// To prevent the closures from intererring with the borrow checking of the surrounding environment, we replace the MIR body of the closure with an empty loop and remove all of the arguments to the closure in the surrounding MIR.
pub(crate) fn cleanup_spec_closures<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &mut Body<'tcx>) {
    trace!("cleanup_spec_closures: {:?}", def_id);

    if no_mir(tcx, def_id) {
        trace!("replacing function body");
        *body.basic_blocks_mut() = make_loop(tcx);
    } else {
        let mut cleanup = NoTranslateNoMoves { tcx, unused: IndexSet::new() };
        cleanup.visit_body(body);

        cleanup_statements(body, &cleanup.unused);
        let map = map_locals(&mut body.local_decls, &cleanup.unused);
        let mut updater = LocalUpdater { map, tcx };
        updater.visit_body(body);

        body.local_decls.shrink_to_fit();
    }
}

fn cleanup_statements<'tcx>(body: &mut Body<'tcx>, unused: &IndexSet<Local>) {
    for data in body.basic_blocks_mut() {
        data.statements.retain(|statement| match &statement.kind {
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                !unused.contains(local)
            }
            StatementKind::PlaceMention(place) => !unused.contains(&place.local),
            StatementKind::Assign(box (place, _)) | StatementKind::FakeRead(box (_, place)) => {
                !unused.contains(&place.local)
            }
            _ => true,
        })
    }
}

pub(crate) fn make_loop(_: TyCtxt) -> IndexVec<BasicBlock, BasicBlockData> {
    let mut body = IndexVec::new();
    body.push(BasicBlockData::new(
        Some(Terminator {
            source_info: SourceInfo::outermost(rustc_span::DUMMY_SP),
            kind: TerminatorKind::Return,
        }),
        false,
    ));
    body
}

pub struct NoTranslateNoMoves<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub unused: IndexSet<Local>,
}

impl<'tcx> MutVisitor<'tcx> for NoTranslateNoMoves<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_body(&mut self, body: &mut Body<'tcx>) {
        self.super_body(body);

        self.unused.retain(|loc| !body.local_decls[*loc].is_user_variable());
    }

    fn visit_rvalue(&mut self, rvalue: &mut Rvalue<'tcx>, l: Location) {
        match rvalue {
            Rvalue::Aggregate(box AggregateKind::Closure(def_id, _), substs) => {
                if is_no_translate(self.tcx, *def_id) || is_snapshot_closure(self.tcx, *def_id) {
                    substs.iter_mut().for_each(|p| {
                        if p.is_move() {
                            let place = p.place().unwrap();
                            if let Some(loc) = place.as_local() {
                                self.unused.insert(loc);
                            }
                        }
                    });
                    *substs = IndexVec::new();
                }
            }
            _ => self.super_rvalue(rvalue, l),
        }
    }
}

pub(crate) fn map_locals<V>(
    local_decls: &mut IndexVec<Local, V>,
    dead_locals: &IndexSet<Local>,
) -> IndexVec<Local, Option<Local>> {
    let mut map: IndexVec<Local, Option<Local>> = IndexVec::from_elem(None, &*local_decls);
    let mut used = Local::new(0);
    for idx in local_decls.indices() {
        if dead_locals.contains(&idx) {
            continue;
        }

        map[idx] = Some(used);
        if idx != used {
            local_decls.swap(idx, used);
        }
        used.increment_by(1);
    }

    local_decls.truncate(used.index());
    map
}

pub struct LocalUpdater<'tcx> {
    pub map: IndexVec<Local, Option<Local>>,
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for LocalUpdater<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_local(&mut self, l: &mut Local, _: PlaceContext, _: Location) {
        *l = self.map[*l].unwrap();
    }
}

pub fn remove_ghost_closures<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    struct RemoveGhostItems<'tcx> {
        tcx: TyCtxt<'tcx>,
    }

    impl<'tcx> MutVisitor<'tcx> for RemoveGhostItems<'tcx> {
        fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn visit_statement(
            &mut self,
            statement: &mut rustc_middle::mir::Statement<'tcx>,
            _: Location,
        ) {
            let StatementKind::Assign(box (_, rhs)) = &statement.kind else { return };
            let Rvalue::Aggregate(box AggregateKind::Closure(def_id, _), _) = rhs else {
                return;
            };
            if is_no_translate(self.tcx, *def_id) || is_snapshot_closure(self.tcx, *def_id) {
                statement.kind = StatementKind::Nop
            }
        }
    }

    RemoveGhostItems { tcx }.visit_body(body);
}
