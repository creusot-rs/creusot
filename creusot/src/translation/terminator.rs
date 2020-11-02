use std::collections::HashMap;

use rustc_middle::{
    mir::{Location, Terminator, TerminatorKind::*},
    ty::VariantDef,
};

use crate::{mlcfg::{MlCfgConstant, MlCfgExp, MlCfgPattern, MlCfgTerminator as MlT}, place::from_place};

use super::{statement::create_assign, FunctionTranslator};

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

                let discr_ty = if let Some(pl) = discr.place() {
                    let discr_local = pl.as_local().unwrap();

                    // Look to see if we can find a discriminator assignment
                    // if not it means that we are switching on a literal
                    self.discr_map
                        .get(&(location.block, discr_local))
                        .unwrap_or(&pl)
                        .ty(self.body, self.tcx)
                        .ty
                } else {
                    discr.constant().unwrap().literal.ty
                };

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
                    Bool => {
                        let discriminant = self.translate_operand(discr);
                        assert!(targets.all_targets().len() == 2);

                        let branches = vec![
                            (MlCfgPattern::LitP(MlCfgConstant::const_false()), targets.all_targets()[0].into()),
                            (MlCfgPattern::LitP(MlCfgConstant::const_true()), targets.all_targets()[1].into()),
                            (MlCfgPattern::Wildcard, targets.otherwise().into()),
                        ];

                        self.emit_terminator(MlT::Switch(discriminant, branches));

                    }
                    Char | Int(_) | Uint(_) | Float(_) => unimplemented!("literal switch"),
                    _ => unimplemented!(),
                }
            }
            Abort => self.emit_terminator(MlT::Absurd),
            Return => self.emit_terminator(MlT::Return),
            Unreachable => self.emit_terminator(MlT::Absurd),
            Call { func, args, destination, .. } => {
                let func_args: Vec<_> =
                    args.iter().map(|arg| self.translate_operand(arg)).collect();

                let fname = self.translate_operand(func);

                let (loc, bb) = destination.unwrap();

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
}

fn variant_pattern(var: &VariantDef) -> MlCfgPattern {
    let wilds = var.fields.iter().map(|_| MlCfgPattern::Wildcard).collect();
    let cons_name = var.ident.to_string();
    MlCfgPattern::ConsP(cons_name, wilds)
}
