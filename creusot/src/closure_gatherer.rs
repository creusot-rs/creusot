use rustc_hir::def_id::DefId;
use rustc_middle::thir::{Expr, ExprKind, Thir};
use rustc_mir_build::thir::visit::{self, Visitor};

use indexmap::IndexSet;

pub struct ClosureGatherer<'a, 'tcx> {
    thir: &'a Thir<'tcx>,
    pub closures: IndexSet<DefId>,
}

impl ClosureGatherer<'a, 'tcx> {
    pub fn new(thir: &'a Thir<'tcx>) -> Self {
        ClosureGatherer { thir, closures: IndexSet::new() }
    }
}

impl Visitor<'a, 'tcx> for ClosureGatherer<'a, 'tcx> {
    fn thir(&self) -> &'a Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &Expr<'tcx>) {
        match expr.kind {
            ExprKind::Closure { closure_id, .. } => {
                self.closures.insert(closure_id);
            }
            _ => {}
        };
        visit::walk_expr(self, expr);
    }
}
