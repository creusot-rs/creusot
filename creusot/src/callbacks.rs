use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Config, Queries};

use crate::cleanup_spec_closures::*;

use crate::options::Options;

pub struct ToWhy {
    opts: Options,
}

impl ToWhy {
    pub fn new(opts: Options) -> Self {
        ToWhy { opts }
    }
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
        })
    }

    fn after_expansion<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries.prepare_outputs().unwrap();

        let _ = queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| crate::translation::translate(tcx, &self.opts));

        c.session().abort_if_errors();

        if self.opts.continue_compilation {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
