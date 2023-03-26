use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Config, Queries};

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

impl Callbacks for ToWhy {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers, _external_providers| {
            providers.mir_built = |tcx, def_id| {
                let mir = (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_spec_closures(tcx, def_id.def_id_for_type_of(), &mut mir);
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
