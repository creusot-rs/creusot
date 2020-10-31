use std::collections::HashMap;

use rustc_middle::{
    mir::{BasicBlock, Location, Place, Rvalue, Terminator, TerminatorKind::*},
    ty::VariantDef,
};

use crate::{place::from_place, mlcfg::{MlCfgExp, MlCfgPattern, MlCfgTerminator as MlT}};

use super::{FunctionTranslator, statement::create_assign, rhs_to_why_exp};

// Translate the terminator of a basic block.
// There isn't much that's special about this. The only subtlety is in how
// we translate switchInt. We rewrite it into a primitive constructor match
// rather than switching on discriminant since WhyML doesn't have integer
// patterns in match expressions.

impl<'tcx> FunctionTranslator<'_, 'tcx> {
    pub fn translate_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            Goto { target } => self.emit_terminator(MlT::Goto(target.into())),
            SwitchInt { discr, targets, .. } => {
                let _ = targets.otherwise();
                use rustc_middle::ty::TyKind::*;
                let _ = targets.otherwise();

                let discr_local = discr.place().and_then(|p| p.as_local()).unwrap();

                let discr_place = self
                    .discr_map
                    .get(&(location.block, discr_local))
                    .expect("constant discriminator");

                let discr_ty = discr_place.ty(self.body, self.tcx).ty;

                match discr_ty.kind() {
                    Adt(def, _) => {
                        let discr_to_var_idx: HashMap<_, _> =
                            def.discriminants(self.tcx).map(|(idx, d)| (d.val, idx)).collect();
                        let mut branches: Vec<_> = targets
                            .iter()
                            .map(|(disc, target)| {
                                (
                                    variant_pattern(&def.variants[discr_to_var_idx[&disc]]),
                                    target.into(),
                                )
                            })
                            .collect();

                        branches.push((MlCfgPattern::Wildcard, targets.otherwise().into()));
                        let discriminant = self.translate_operand(discr);

                        self.emit_terminator(MlT::Switch(discriminant, branches));
                    }
                    Tuple(_) => unimplemented!("tuple"),

                    Bool | Char | Int(_) | Uint(_) | Float(_) => unimplemented!("literal switch"),
                    _ => unimplemented!(),
                }
            }
            Abort => { self.emit_terminator(MlT::Absurd) }
            Return => self.emit_terminator(MlT::Return),
            Unreachable => self.emit_terminator(MlT::Absurd),
            Call { func, args, destination, .. } => {
                let func_args : Vec<_> = args.iter()
                    .map(|arg| self.translate_operand(arg))
                    .collect();

                let fname = self.translate_operand(func);

                let (loc, bb) = destination.unwrap();
                use crate::mlcfg::MlCfgStatement as MlS;

                let call = MlCfgExp::Call(box fname, func_args);
                let call_stmt = create_assign(&from_place(self.tcx, self.body, &loc), call);

                self.emit_statement(call_stmt);

                self.emit_terminator(MlT::Goto(bb.into()));

            }
            Assert { cond: _, expected: _, msg: _, target: _, cleanup: _ } => {}

            FalseEdge { real_target, .. } => self.emit_terminator(MlT::Goto(real_target.into())),

            // Not handled
            Drop { .. }
            | DropAndReplace { .. }
            | Yield { .. }
            | Resume
            | GeneratorDrop
            | FalseUnwind { .. }
            | InlineAsm { .. } => unreachable!(),
        }
    }

    // Return the place that holds the discriminator (assuming there is one).
    fn get_discriminator_place(&self, bb: BasicBlock) -> &Place<'tcx> {
        let statement = self.body.basic_blocks()[bb].statements.last();
        use rustc_middle::mir::StatementKind::*;
        if let Some(Assign(box (_, rval))) = statement.map(|s| &s.kind) {
            match rval {
                Rvalue::Discriminant(pl) => pl,
                _ => unimplemented!("constant match"),
            }
        } else {
            panic!("expected discriminant as last statement of block");
        }
    }
}

fn variant_pattern(var: &VariantDef) -> MlCfgPattern {
    let wilds = var.fields.iter().map(|_| MlCfgPattern::Wildcard).collect();
    let cons_name = var.ident.to_string();
    MlCfgPattern::ConsP(cons_name, wilds)
}
