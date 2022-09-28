use creusot_rustc::{
    hir::def_id::DefId,
    index::vec::IndexVec,
    middle::{
        mir::{Terminator, TerminatorKind},
        ty::TyCtxt,
    },
    smir::mir::{
        AggregateKind, BasicBlock, BasicBlockData, Body, Local, Location, MutVisitor, Rvalue,
        SourceInfo,
    },
};
use indexmap::IndexSet;

use crate::util;

/// Hide non-linear specification code from the borrow checker
///
/// Specifications in Creusot are encoded inside of special closures that are inserted throughout the code.
/// The code inside those closures is meant to be Pearlite and is thus not subject to Rust's borrow checker, however it needs to be able to refer to normal Rust variables.
/// To prevent the closures from intererring with the borrow checking of the surrounding environment, we replace the MIR body of the closure with an empty loop and remove all of the arguments to the closure in the surrounding MIR.
pub(crate) fn cleanup_spec_closures<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &mut Body<'tcx>) {
    trace!("cleanup_spec_closures: {:?}", def_id);
    if util::no_mir(tcx, def_id) {
        trace!("replacing function body");
        *body.basic_blocks_mut() = make_loop(tcx);
        body.var_debug_info = Vec::new();
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
    use creusot_rustc::smir::mir::StatementKind;

    for data in body.basic_blocks_mut() {
        data.statements.retain(|statement| match &statement.kind {
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                !unused.contains(local)
            }
            StatementKind::Assign(box (place, _)) => !unused.contains(&place.local),
            _ => true,
        })
    }
}

pub(crate) fn make_loop(_: TyCtxt) -> IndexVec<BasicBlock, BasicBlockData> {
    let mut body = IndexVec::new();
    body.push(BasicBlockData::new(Some(Terminator {
        source_info: SourceInfo::outermost(creusot_rustc::span::DUMMY_SP),
        kind: TerminatorKind::Return,
    })));
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
                if util::is_no_translate(self.tcx, def_id.to_def_id())
                    || util::is_ghost(self.tcx, def_id.to_def_id())
                {
                    substs.iter_mut().for_each(|p| {
                        if p.is_move() {
                            self.unused.insert(p.place().unwrap().as_local().unwrap());
                        }
                    });
                    *substs = Vec::new();
                }
            }
            _ => self.super_rvalue(rvalue, l),
        }
    }
}

use creusot_rustc::index::vec::Idx;

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

use creusot_rustc::middle::mir::visit::PlaceContext;

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
