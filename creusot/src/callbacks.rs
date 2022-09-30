use creusot_rustc::{
    driver::{Callbacks, Compilation},
    interface::{interface::Compiler, Config, Queries},
};

use crate::{cleanup_spec_closures::*, options::Options};

pub struct ToWhy {
    opts: Options,
}

impl ToWhy {
    pub fn new(opts: Options) -> Self {
        ToWhy { opts }
    }
}
use crate::ctx;

impl Callbacks for ToWhy {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers, _external_providers| {
            providers.mir_built = |tcx, def_id| {
                let mir =
                    (creusot_rustc::interface::DEFAULT_QUERY_PROVIDERS.mir_built)(tcx, def_id);
                let mut mir = mir.steal();
                cleanup_spec_closures(tcx, def_id.def_id_for_type_of(), &mut mir);
                tcx.alloc_steal_mir(mir)
            };
        })
    }

    fn after_expansion<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries.prepare_outputs().unwrap();
        queries.global_ctxt().unwrap();

        let _ = queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
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
