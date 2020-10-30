use rustc_middle::mir::{Statement, StatementKind::*};

use super::FunctionTranslator;

impl<'tcx> FunctionTranslator<'_, 'tcx> {
    pub fn translate_statement(&self, statement: &'_ Statement<'tcx>) {}
}
