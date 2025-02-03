use rustc_borrowck::consumers::{BodyWithBorrowckFacts, ConsumerOptions};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::{interface::Compiler, Config};
use rustc_middle::ty::TyCtxt;

use std::{cell::RefCell, collections::HashMap, thread_local};

use crate::{
    cleanup_spec_closures::*,
    ctx, lints,
    options::{Options, Output},
};

pub struct ToWhy {
    opts: Options,
}

const OUTPUT_PREFIX: &str = "verif";

impl ToWhy {
    pub fn new(opts: Options) -> Self {
        ToWhy { opts }
    }

    // Isolate every crate in its own directory `{crate_name}-{crate_type}`.
    fn set_output_dir(&mut self, config: &Config) {
        let Output::Directory(ref mut dir) = self.opts.output else { return }; // if we're given a specific output file, just use that
        if config.opts.crate_types.len() > 1 {
            warn!(
                "Found more than one --crate-type, only the first one will be used: {:?}",
                config.opts.crate_types
            );
        }
        let mut krate = match &config.opts.crate_name {
            Some(krate) => krate.clone(),
            None => {
                warn!("No crate name found, defaulting to 'a'");
                "a".to_string()
            }
        };
        match config.opts.crate_types.get(0) {
            None => {}
            Some(crate_type) => {
                krate = krate + "_" + &crate_type.to_string();
            }
        };
        if self.opts.monolithic {
            // output file: "verif/{krate}.coma"
            dir.push(OUTPUT_PREFIX);
            dir.push(krate + ".coma");
            self.opts.output = Output::File(dir.clone());
        } else {
            // prefix: "verif/{krate}/"
            self.opts.prefix = vec![why3::Ident::build(OUTPUT_PREFIX), why3::Ident::build(&krate)];
        }
    }
}

thread_local! {
    pub static MIR_BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

impl Callbacks for ToWhy {
    fn config(&mut self, config: &mut Config) {
        self.set_output_dir(config);

        // HACK: remove this once `config.locale_resources` is defined as a Vec
        let mut locale_resources = config.locale_resources.to_vec();
        locale_resources.push(crate::DEFAULT_LOCALE_RESOURCE);
        config.locale_resources = locale_resources;
        config.override_queries = Some(|_sess, providers| {
            providers.mir_built = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_spec_closures(tcx, def_id.to_def_id(), &mut mir);
                tcx.alloc_steal_mir(mir)
            };

            providers.mir_drops_elaborated_and_const_checked = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS
                    .mir_drops_elaborated_and_const_checked)(tcx, def_id);
                let mut mir = mir.steal();
                remove_ghost_closures(tcx, &mut mir);
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

    fn after_expansion<'tcx>(&mut self, c: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut ctx = ctx::TranslationCtx::new(tcx, self.opts.clone());
        let _ = crate::translation::before_analysis(&mut ctx);
        let _ = tcx.analysis(());
        let _ = crate::translation::after_analysis(ctx);

        c.sess.dcx().abort_if_errors();

        if self.opts.in_cargo {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

/// Try to retrieve the promoted MIR for a body from a thread local cache.
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
