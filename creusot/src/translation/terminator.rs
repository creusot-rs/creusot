use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::mir::BasicBlock;
use rustc_middle::{
    mir::{Location, Operand, Terminator, TerminatorKind::*},
    ty::{self, VariantDef},
};

use crate::{
    mlcfg::{Constant, Exp, Pattern, Terminator as MlT},
    place::from_place,
};

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
                let real_discr = discriminator_for_switch(&self.body.basic_blocks()[location.block])
                    .map(Operand::Move)
                    .unwrap_or_else(||discr.clone());

                let (discrs, normal_targets) : (_, Vec<BasicBlock>) = targets.iter().unzip();
                let branch_pats = branches_for_ty(self.tcx, real_discr.ty(self.body, self.tcx), discrs);

                let mut branches : Vec<_> = branch_pats.into_iter().zip(normal_targets.iter().map(|t| t.into())).collect();

                branches.push((Pattern::Wildcard, targets.otherwise().into()));
                let discriminant = self.translate_operand(&real_discr);

                self.emit_terminator(MlT::Switch(discriminant, branches));
            }
            Abort => self.emit_terminator(MlT::Absurd),
            Return => self.emit_terminator(MlT::Return),
            Unreachable => self.emit_terminator(MlT::Absurd),
            Call { func, args, destination, .. } => {
                let fun_def_id = func_defid(func).expect("expected call with function");

                let mut func_args: Vec<_> =
                    args.iter().map(|arg| self.translate_operand(arg)).collect();

                let call_exp = if self.is_box_new(fun_def_id) {
                    assert_eq!(func_args.len(), 1);

                    func_args.remove(0)
                } else {
                    let fname = self.translate_operand(func);
                    Exp::Call(box fname, func_args)
                };

                if destination.is_none() {
                    // If we have no target block after the call, then we cannot move past it.
                    self.emit_terminator(MlT::Absurd);
                    return;
                } else {
                    let (loc, bb) = destination.unwrap();
                    let call_stmt = create_assign(&from_place(self.tcx, self.body, &loc), call_exp);
                    self.emit_statement(call_stmt);
                    self.emit_terminator(MlT::Goto(bb.into()));
                }
            }
            Assert { cond: _, expected: _, msg: _, target: _, cleanup: _ } => {
                unimplemented!("assert")
            }

            FalseEdge { real_target, .. } => self.emit_terminator(MlT::Goto(real_target.into())),

            // TODO: Do we really need to do anything more?
            Drop { target, .. } => self.emit_terminator(MlT::Goto(target.into())),
            Resume => {
                log::debug!("Skipping resume terminator");
            }
            FalseUnwind { real_target, .. } => {
                self.emit_terminator(MlT::Goto(real_target.into()));
            }
            DropAndReplace { .. } | Yield { .. } | GeneratorDrop | InlineAsm { .. } => {
                unreachable!("{:?}", terminator.kind)
            }
        }
    }

    fn is_box_new(&self, def_id: DefId) -> bool {
        self.tcx.def_path_str(def_id) == "std::boxed::Box::<T>::new"
    }
}

// Try to extract a function defid from an operand
fn func_defid<'tcx>(op: &Operand<'tcx>) -> Option<DefId> {
    let fun_ty = op.constant().unwrap().literal.ty;
    if let ty::TyKind::FnDef(def_id, _) = fun_ty.kind() {
        Some(*def_id)
    } else {
        None
    }
}


use rustc_middle::mir::{TerminatorKind, BasicBlockData, Place, Rvalue, StatementKind};
use rustc_middle::ty::{Ty, TyCtxt};

// Find the place being discriminated, if there is one
pub fn discriminator_for_switch<'tcx>(bbd: &BasicBlockData<'tcx>) -> Option<Place<'tcx>> {
    let discr = if let TerminatorKind::SwitchInt { discr, .. } = &bbd.terminator().kind {
        discr
    } else {
        return None;
    };

    if let StatementKind::Assign(box (pl, Rvalue::Discriminant(real_discr))) =
        bbd.statements.last().unwrap().kind
    {
        if discr.place() == Some(pl) {
            Some(real_discr)
        } else {
            None
        }
    } else {
        None
    }
}

// Create the patterns for a switch
pub fn branches_for_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    switch_ty: Ty<'tcx>,
    targets: Vec<u128>,
) -> Vec<Pattern> {
    use rustc_middle::ty::TyKind::*;
    match switch_ty.kind() {
        Adt(def, _) => {
            let discr_to_var_idx: HashMap<_, _> =
                def.discriminants(tcx).map(|(idx, d)| (d.val, idx)).collect();

            targets
                .iter()
                .map(|disc| variant_pattern(&def.variants[discr_to_var_idx[&disc]]))
                .collect()
        }
        Tuple(_) => unimplemented!("tuple"),
        Bool => vec![Pattern::LitP(Constant::const_false()), Pattern::LitP(Constant::const_true())],
        _ => unimplemented!("constant pattern"),
    }
}

pub fn variant_pattern(var: &VariantDef) -> Pattern {
    let wilds = var.fields.iter().map(|_| Pattern::Wildcard).collect();
    let cons_name = var.ident.to_string();
    Pattern::ConsP(cons_name, wilds)
}
