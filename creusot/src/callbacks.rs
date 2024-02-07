use rustc_borrowck::consumers::{BodyWithBorrowckFacts, ConsumerOptions};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::{interface::Compiler, Config, Queries};
use rustc_middle::ty::TyCtxt;

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

thread_local! {
    pub static MIR_BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

impl Callbacks for ToWhy {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers| {
            providers.mir_built = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_spec_closures(tcx, def_id.to_def_id(), &mut mir);
                tcx.alloc_steal_mir(mir)
            };

            providers.mir_borrowck = |tcx, def_id| {
                let opts = ConsumerOptions::RegionInferenceContext;

                let body_with_facts =
                    rustc_borrowck::consumers::get_body_with_borrowck_facts(tcx, def_id, opts);

                // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
                let body_with_facts: BodyWithBorrowckFacts<'static> =
                    unsafe { std::mem::transmute(body_with_facts) };

                MIR_BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    assert!(map.insert(def_id, body_with_facts).is_none());
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

/// Trys to retrieve the promoted MIR for a body from a thread local cache.
/// The cache is populated when rustc runs the `mir_borrowck` query.
/// After a body was retrieved, calling this function again for the same `def_id` will return `None`.
pub fn get_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<BodyWithBorrowckFacts<'tcx>> {
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
