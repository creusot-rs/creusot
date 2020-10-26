use rustc_middle::mir::{Terminator, TerminatorKind::*};

use super::TranslationCtx;

impl<'tcx> TranslationCtx<'tcx> {
    pub fn term_to_why(term: &Terminator<'tcx>) -> () {
        match &term.kind {
            Goto { target } => {}
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
