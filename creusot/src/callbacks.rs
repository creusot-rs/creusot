use rustc_borrowck::consumers::{BodyWithBorrowckFacts, ConsumerOptions};
use rustc_data_structures::fx::FxHashMap;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_interface::{Config, interface::Compiler};
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::ErrorGuaranteed;

use std::{cell::RefCell, collections::HashMap, thread_local};

use crate::{
    cleanup_spec_closures::*,
    lints,
    metadata::BinaryMetadata,
    validate::{AnfBlock, a_normal_form_without_specs},
};
use creusot_args::options::{Options, Output};

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
            self.opts.prefix = vec![OUTPUT_PREFIX.into(), krate];
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

            providers.mir_borrowck = |tcx, def_id| mir_borrowck(tcx, def_id);
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
        let params_open_inv = crate::translation::before_analysis(tcx);
        let _ = tcx.analysis(());
        let _ = crate::translation::after_analysis(tcx, self.opts.clone(), params_open_inv);

        c.sess.dcx().abort_if_errors();

        if self.opts.in_cargo { Compilation::Continue } else { Compilation::Stop }
    }
}

fn mir_borrowck<'tcx, 'a>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Result<&'a mir::DefinitionSiteHiddenTypes<'tcx>, ErrorGuaranteed> {
    let opts = ConsumerOptions::RegionInferenceContext;
    let bodies_with_facts =
        rustc_borrowck::consumers::get_bodies_with_borrowck_facts(tcx, def_id, opts);

    // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
    let bodies_with_facts: FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>> =
        unsafe { std::mem::transmute(bodies_with_facts) };

    MIR_BODIES.with(|state| {
        let mut map = state.borrow_mut();
        for (def_id, mut body) in bodies_with_facts {
            // We need to remove false edges. They are used in compilation of pattern matchings
            // in ways that may result in move paths that are marked live and uninitilized at the
            // same time. We cannot handle this in the generation of resolution.
            // On the other hand, it is necessary to keep false unwind edges, because they are needed
            // by liveness analysis.
            for bbd in body.body.basic_blocks_mut().iter_mut() {
                let term = bbd.terminator_mut();
                if let mir::TerminatorKind::FalseEdge { real_target, .. } = term.kind {
                    term.kind = mir::TerminatorKind::Goto { target: real_target };
                }
            }
            assert!(map.insert(def_id, body).is_none());
        }
    });

    (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_borrowck)(tcx, def_id)
}

/// Try to retrieve the promoted MIR for a body from a thread local cache.
/// The cache is populated when rustc runs the `mir_borrowck` query.
/// After a body was retrieved, calling this function again for the same `def_id` will return `None`.
pub fn get_body<'tcx, 'a>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> &'a BodyWithBorrowckFacts<'tcx> {
    if let Some(body) = try_get_body(def_id) {
        return body;
    }

    // trigger borrow checking on the root element
    let root = tcx.typeck_root_def_id(def_id.to_def_id()).expect_local();
    let _ = tcx.mir_borrowck(root);

    try_get_body(def_id)
        .unwrap_or_else(|| panic!("Could not find body for {:?}", tcx.def_path_str(def_id)))
}

/// Just try to `get` from `MIR_BODIES`
fn try_get_body<'tcx, 'a>(def_id: LocalDefId) -> Option<&'a BodyWithBorrowckFacts<'tcx>> {
    MIR_BODIES.with(|state| {
        let map = state.borrow();
        map.get(&def_id).map(|body| unsafe { std::mem::transmute(body) })
    })
}

/// Callback for libraries that don't depend on creusot-contracts, to store metadata needed in later passes
pub struct WithoutContracts {
    opts: Options,
}

impl WithoutContracts {
    pub fn new(opts: Options) -> Self {
        WithoutContracts { opts }
    }
}

impl Callbacks for WithoutContracts {
    fn after_expansion<'tcx>(&mut self, c: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        if self.opts.erasure_check.is_no() {
            return Compilation::Continue;
        }
        let Some(erasure_check_dir) = &self.opts.erasure_check_dir else {
            return Compilation::Continue;
        };
        let erasure_required = crate::metadata::get_erasure_required(tcx, erasure_check_dir);
        if erasure_required.is_empty() {
            return Compilation::Continue;
        }
        let erased_thir: Vec<(DefId, AnfBlock<'tcx>)> = tcx
            .hir_body_owners()
            .filter_map(|local_id| {
                if erasure_required.contains(&local_id) {
                    let erased =
                        a_normal_form_without_specs(tcx, local_id, self.opts.erasure_check)?;
                    Some((local_id.to_def_id(), erased))
                } else {
                    None
                }
            })
            .collect();
        if let Some(err) = c.sess.dcx().has_errors_or_delayed_bugs() {
            err.raise_fatal()
        }
        let metadata = BinaryMetadata::without_specs(erased_thir);
        crate::metadata::dump_exports(tcx, &Default::default(), metadata);
        Compilation::Continue
    }
}
