use once_map::OnceMap;
use rustc_borrowck::consumers::{
    BorrowIndex, BorrowSet, ConsumerOptions, calculate_borrows_out_of_scope_at_location,
};
use rustc_data_structures::fx::FxIndexMap;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_interface::{Config, interface::Compiler};
use rustc_middle::{mir, ty::TyCtxt};

use std::sync::LazyLock;

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

/// Bodies produced by `mir_borrowck`, leaked so that `get_body` can release the lock.
/// This `static` also serves as a compile-time check that `BorrowckBody: Sync`.
static MIR_BODIES: LazyLock<OnceMap<LocalDefId, &'static BorrowckBody<'static>>> =
    LazyLock::new(OnceMap::new);

/// The parts of [`BodyWithBorrowckFacts`] that Creusot needs.
///
/// Unlike `BodyWithBorrowckFacts`, this is `Send` and `Sync`: we drop the `RegionInferenceContext`
/// (which contains `Rc`s) after extracting the information we need from it.
pub(crate) struct BorrowckBody<'tcx> {
    pub(crate) body: mir::Body<'tcx>,
    pub(crate) promoted: IndexVec<mir::Promoted, mir::Body<'tcx>>,
    pub(crate) borrow_set: BorrowSet<'tcx>,
    pub(crate) borrows_out_of_scope_at_location: FxIndexMap<mir::Location, Vec<BorrowIndex>>,
}

impl Callbacks for ToWhy {
    fn config(&mut self, config: &mut Config) {
        self.set_output_dir(config);

        config.override_queries = Some(|_sess, providers| {
            // Remove MIR of Pearlite code (logic functions, contracts, assertions, snapshots)
            // One might wonder why not override `mir_promoted` instead: that would be too late because
            // drops are inserted then, and that results in errors because many types are not Drop.
            providers.queries.mir_built = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_spec_closures(tcx, def_id, &mut mir);
                tcx.alloc_steal_mir(mir)
            };

            // Store borrow-checked bodies for translation
            providers.queries.mir_borrowck = |tcx, local_id| {
                copy_mir_bodies(tcx, local_id);
                (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.mir_borrowck)(tcx, local_id)
            };

            // The `check_liveness` query is where unused variable warnings are emitted.
            // We reintroduce the MIR of Pearlite code for this analysis.
            // Then we remove it again for good.
            providers.queries.check_liveness = |tcx, local_id| {
                // Make sure borrow checking is done before restoring the MIR,
                // otherwise the borrow checker could miss it concurrently.
                tcx.ensure_ok().mir_borrowck(tcx.typeck_root_def_id_local(local_id));
                restore_mir_for_liveness_check(tcx, local_id);
                let value = (rustc_interface::DEFAULT_QUERY_PROVIDERS.queries.check_liveness)(
                    tcx, local_id,
                );
                cleanup_spec_closures_final(tcx, local_id);
                value
            };

            // Remove ghost code for codegen
            providers.queries.mir_drops_elaborated_and_const_checked = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS
                    .queries
                    .mir_drops_elaborated_and_const_checked)(tcx, def_id);
                let mut mir = mir.steal();
                remove_ghost_closures(tcx, &mut mir);
                tcx.alloc_steal_mir(mir)
            };
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
        rustc_interface::passes::full_analysis(tcx);
        let _ = crate::translation::after_analysis(tcx, self.opts.clone(), params_open_inv);

        c.sess.dcx().abort_if_errors();

        if self.opts.in_cargo { Compilation::Continue } else { Compilation::Stop }
    }
}

fn copy_mir_bodies<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) {
    let opts = ConsumerOptions::RegionInferenceContext;
    tcx.dcx().abort_if_errors(); // The following can crash if we did not pass type-checking
    let bodies_with_facts =
        rustc_borrowck::consumers::get_bodies_with_borrowck_facts(tcx, def_id, opts);

    for (def_id, mut body) in bodies_with_facts {
        // We need to remove false edges. They are used in compilation of pattern matchings
        // in ways that may result in move paths that are marked live and uninitilized at the
        // same time. We cannot handle this in the generation of resolution.
        // On the other hand, it is necessary to keep false unwind edges, because they are needed
        // by liveness analysis.
        for bbd in body.body.basic_blocks_mut().iter_mut() {
            let term = bbd.terminator_mut();
            if let mir::TerminatorKind::FalseEdge { real_target, .. } = term.kind {
                term.kind = mir::TerminatorKind::Goto {
                    target: real_target,
                    loop_hint_attrs: Default::default(),
                };
            }
        }
        let borrows_out_of_scope_at_location = calculate_borrows_out_of_scope_at_location(
            &body.body,
            &body.region_inference_context,
            &body.borrow_set,
        );
        let body = BorrowckBody {
            body: body.body,
            promoted: body.promoted,
            borrow_set: body.borrow_set,
            borrows_out_of_scope_at_location,
        };
        // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
        let body: BorrowckBody<'static> = unsafe { std::mem::transmute(body) };
        MIR_BODIES.insert(def_id, |_| Box::leak(Box::new(body)));
    }
}

/// Try to retrieve the promoted MIR for a body from a global cache.
/// The cache is populated when rustc runs the `mir_borrowck` query.
pub(crate) fn get_body<'tcx, 'a>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> &'a BorrowckBody<'tcx> {
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
fn try_get_body<'tcx, 'a>(def_id: LocalDefId) -> Option<&'a BorrowckBody<'tcx>> {
    let body = MIR_BODIES.get(&def_id)?;
    // SAFETY: The 'static lifetime is cast back to the actual lifetime 'tcx.
    Some(unsafe { std::mem::transmute(body) })
}

/// Callback for libraries that don't depend on creusot-std, to store metadata needed in later passes
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
        c.sess.dcx().abort_if_errors();
        // Metadata encoding requires `commit_end_of_determinism` to have been called,
        // which happens during `analysis`.
        rustc_interface::passes::full_analysis(tcx);
        let metadata = BinaryMetadata::without_specs(erased_thir);
        crate::metadata::dump_exports(tcx, &Default::default(), metadata);
        Compilation::Continue
    }
}
