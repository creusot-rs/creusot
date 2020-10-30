use rustc_middle::mir::{Location, Terminator, TerminatorKind::*, visit::Visitor};

use super::FunctionTranslator;

impl<'tcx> FunctionTranslator<'_, 'tcx> {
    pub fn translate_terminator(&mut self, terminator: &Terminator< 'tcx>) {
        match &terminator.kind {
            Goto { target } => {

            }
            SwitchInt { discr, switch_ty, targets, .. } => {}
            Abort => {}
            Return => {}
            Unreachable => {}
            Drop { place, target, unwind } => {}
            Call { func, args, destination, cleanup, from_hir_call, fn_span } => {}
            Assert { cond, expected, msg, target, cleanup } => {}
            // Not handled
            DropAndReplace { .. }
            | Yield { .. }
            | Resume
            | GeneratorDrop
            | FalseEdge { .. }
            | FalseUnwind { .. }
            | InlineAsm { .. } => unreachable!(),
        }
    }
}
