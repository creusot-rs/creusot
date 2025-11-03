use crate::contracts_items::{is_logic, is_no_translate, is_opaque};
use indexmap::IndexSet;
use rustc_abi::FieldIdx;
use rustc_data_structures::sync::RwLock;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::{Idx, IndexVec};
use rustc_middle::{
    mir::{
        self, AggregateKind, BasicBlock, BasicBlockData, Body, Local, Location, Rvalue, SourceInfo,
        StatementKind, Terminator, TerminatorKind,
        visit::{MutVisitor, PlaceContext},
    },
    ty::TyCtxt,
};
use std::{cell::RefCell, collections::HashMap};

thread_local! {
    pub static PEARLITE_MIR:
        RefCell<HashMap<LocalDefId, IndexVec<BasicBlock, BasicBlockData<'static>>>> =
        RefCell::new(HashMap::new());

    pub static REMOVED_MIR:
        RefCell<HashMap<LocalDefId, RemovedMir<'static>>> =
        RefCell::new(HashMap::new());
}

pub(crate) fn restore_mir_for_liveness_check<'tcx>(tcx: TyCtxt<'tcx>, local_id: LocalDefId) {
    let def_id = local_id.to_def_id();
    let (mir, _) = tcx.mir_promoted(local_id);
    // This is a terrible hack but it shouldn't affect correctness:
    // we've already copied MIR bodies right after borrow checking.
    // This is only used for warnings about unused variables.
    let mut mir = mir.risky_hack_borrow_mut();
    if is_no_translate(tcx, def_id) || is_logic(tcx, def_id) {
        if is_opaque(tcx, def_id) {
            return;
        }
        PEARLITE_MIR.with(|map| {
            // SAFETY: The target lifetime 'tcx is the actual lifetime of the data before it was put in PEARLITE_MIR.
            *mir.basic_blocks_mut() =
                unsafe { std::mem::transmute(map.borrow_mut().remove(&local_id).unwrap()) };
        });
    } else {
        // SAFETY: The target lifetime 'tcx is the actual lifetime of the data before it was put in PEARLITE_MIR.
        let removed = REMOVED_MIR.with(|map| unsafe {
            std::mem::transmute(map.borrow_mut().remove(&local_id).unwrap())
        });
        restore_statements(&mut mir, removed);
    }
}

/// Hide non-linear specification code from the borrow checker
///
/// Specifications in Creusot are encoded inside of special closures that are inserted throughout the code.
/// The code inside those closures is meant to be Pearlite and is thus not subject to Rust's borrow checker, however it needs to be able to refer to normal Rust variables.
/// To prevent the closures from intererring with the borrow checking of the surrounding environment, we replace the MIR body of the closure with an empty loop and remove all of the arguments to the closure in the surrounding MIR.
pub(crate) fn cleanup_spec_closures<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_id: LocalDefId,
    body: &mut Body<'tcx>,
) {
    cleanup_spec_closures_(tcx, local_id, body, true)
}

/// Like `cleanup_spec_closures` but don't write into `PEARLITE_MIR` or `REMOVED_MIR`.
pub(crate) fn cleanup_spec_closures_final<'tcx>(tcx: TyCtxt<'tcx>, local_id: LocalDefId) {
    let (mir, _) = tcx.mir_promoted(local_id);
    let mut mir = mir.risky_hack_borrow_mut();
    cleanup_spec_closures_(tcx, local_id, &mut mir, false);
}

fn cleanup_spec_closures_<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_id: LocalDefId,
    body: &mut Body<'tcx>,
    remember: bool,
) {
    trace!("cleanup_spec_closures: {:?}", local_id);
    let def_id = local_id.to_def_id();

    if is_no_translate(tcx, def_id) || is_logic(tcx, def_id) {
        trace!("replacing function body");
        let bb = std::mem::replace(body.basic_blocks_mut(), make_loop());
        if remember {
            PEARLITE_MIR.with(|map| {
                // SAFETY: Consumers cast the lifetime back to 'tcx
                let bb = unsafe { std::mem::transmute(bb) };
                map.borrow_mut().insert(local_id, bb);
            });
        }
    } else {
        let mut cleanup = NoTranslateNoMoves::new(tcx);
        cleanup.visit_body(body);
        let closures = cleanup.closures;
        let assigns = cleanup_statements(body, &cleanup.unused);
        if remember {
            REMOVED_MIR.with(|map| {
                // SAFETY: Consumers cast the lifetime back to 'tcx
                let removed = unsafe { std::mem::transmute(RemovedMir { closures, assigns }) };
                map.borrow_mut().insert(local_id, removed);
            });
        }
    }
}

struct RemovedMir<'tcx> {
    closures: SpecClosures<'tcx>,
    assigns: SpecAssigns<'tcx>,
}

type SpecClosures<'tcx> = HashMap<DefId, IndexVec<FieldIdx, mir::Operand<'tcx>>>;
type SpecAssigns<'tcx> = HashMap<Local, Vec<(mir::Place<'tcx>, Rvalue<'tcx>)>>;

fn cleanup_statements<'tcx>(body: &mut Body<'tcx>, unused: &IndexSet<Local>) -> SpecAssigns<'tcx> {
    let mut assigns: SpecAssigns = HashMap::new();
    for data in body.basic_blocks_mut() {
        data.statements.retain(|statement| match &statement.kind {
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                !unused.contains(local)
            }
            StatementKind::PlaceMention(place) => !unused.contains(&place.local),
            StatementKind::Assign(box (place, rvalue)) => {
                let dropped = unused.contains(&place.local);
                if dropped {
                    assigns.entry(place.local).or_insert(Vec::new()).push((*place, rvalue.clone()));
                }
                !dropped
            }
            StatementKind::FakeRead(box (_, place)) => !unused.contains(&place.local),
            _ => true,
        })
    }
    assigns
}

fn restore_statements<'tcx>(body: &mut Body<'tcx>, mut removed: RemovedMir<'tcx>) {
    for data in body.basic_blocks_mut() {
        let old_statements = std::mem::take(&mut data.statements);
        for mut s in old_statements {
            if let Some((_, rvalue)) = s.kind.as_assign_mut()
                && let Rvalue::Aggregate(box AggregateKind::Closure(def_id, _), substs) = rvalue
                && let Some(old_substs) = removed.closures.remove(def_id)
            {
                *substs = old_substs;
                for p in substs.iter() {
                    if p.is_move() {
                        let place = p.place().unwrap();
                        if let Some(local) = place.as_local() {
                            let Some(assigns) = removed.assigns.remove(&local) else {
                                continue;
                            };
                            for (place, rvalue) in assigns {
                                data.statements.push(mir::Statement::new(
                                    s.source_info,
                                    StatementKind::Assign(Box::new((place, rvalue))),
                                ))
                            }
                        }
                    }
                }
            }
            data.statements.push(s);
        }
    }
}

pub(crate) fn make_loop<'tcx>() -> IndexVec<BasicBlock, BasicBlockData<'tcx>> {
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
    pub closures: SpecClosures<'tcx>,
}

impl<'tcx> NoTranslateNoMoves<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx, unused: IndexSet::new(), closures: HashMap::new() }
    }
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
                if is_no_translate(self.tcx, *def_id) {
                    for p in substs.iter() {
                        if p.is_move() {
                            let place = p.place().unwrap();
                            if let Some(loc) = place.as_local() {
                                self.unused.insert(loc);
                            }
                        }
                    }
                    self.closures.insert(*def_id, std::mem::take(substs));
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
            if is_no_translate(self.tcx, *def_id) {
                statement.kind = StatementKind::Nop
            }
        }
    }

    RemoveGhostItems { tcx }.visit_body(body);
}
