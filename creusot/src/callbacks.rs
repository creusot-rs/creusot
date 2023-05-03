use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_index::vec::IndexVec;
use rustc_interface::{interface::Compiler, Config, Queries};
use rustc_middle::{
    mir::{Body, Promoted},
    ty::{self, TyCtxt},
};

use std::{cell::RefCell, collections::HashMap, thread_local};

use crate::{cleanup_spec_closures::*, options::Options};

pub struct ToWhy {
    opts: Options,
}

impl ToWhy {
    pub fn new(opts: Options) -> Self {
        ToWhy { opts }
    }
}
use crate::{ctx, lints};

#[derive(Clone)]
pub struct BodyAndPromoteds<'tcx> {
    pub(crate) body: Body<'tcx>,
    pub(crate) promoted: IndexVec<Promoted, Body<'tcx>>,
}

thread_local! {
    pub static MIR_BODIES:
        RefCell<HashMap<LocalDefId, BodyAndPromoteds<'static>>> =
        RefCell::new(HashMap::new());
}

impl Callbacks for ToWhy {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers, _external_providers| {
            providers.mir_built = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_spec_closures(tcx, def_id.def_id_for_type_of(), &mut mir);
                tcx.alloc_steal_mir(mir)
            };

            providers.mir_borrowck = |tcx, def_id| {
                // We use `mir_promoted` as it is the MIR required by borrowck
                let (body, promoted) = tcx.mir_promoted(ty::WithOptConstParam::unknown(def_id));
                let body_and_proms = BodyAndPromoteds {
                    body: body.borrow().clone(),
                    promoted: promoted.borrow().clone(),
                };

                // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
                let body_and_proms: BodyAndPromoteds<'static> =
                    unsafe { std::mem::transmute(body_and_proms) };

                MIR_BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    assert!(map.insert(def_id, body_and_proms).is_none());
                });

                (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_borrowck)(tcx, def_id)
            }
            // TODO override mir_borrowck_const_arg
        });

        let previous = config.register_lints.take();
        config.register_lints = Some(Box::new(move |sess, lint_store| {
            if let Some(previous) = &previous {
                (previous)(sess, lint_store);
            }
            lints::register_lints(sess, lint_store)
        }))
    }

    fn after_expansion<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries.global_ctxt().unwrap();
        let _ = queries.global_ctxt().unwrap().enter(|tcx| {
            let mut ctx = ctx::TranslationCtx::new(tcx, self.opts.clone());
            let _ = crate::translation::before_analysis(&mut ctx);
            let _ = tcx.analysis(());

            let _ = crate::translation::after_analysis(ctx);
        });

        c.session().abort_if_errors();

        if self.opts.in_cargo {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

pub fn get_body<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Option<BodyAndPromoteds<'tcx>> {
    // trigger borrow checking
    let _ = tcx.mir_borrowck(def_id);

    MIR_BODIES.with(|state| {
        let mut map = state.borrow_mut();
        // SAFETY: For soundness we need to ensure that the bodies have
        // the same lifetime (`'tcx`), which they had before they were
        // stored in the thread local.
        map.remove(&def_id).map(|body| unsafe { std::mem::transmute(body) })
    })
}
