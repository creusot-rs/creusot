use std::collections::HashMap;

use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Location, Operand, Terminator, TerminatorKind::*},
    ty,
};
use rustc_middle::{
    mir::{SourceInfo, SwitchTargets},
    ty::AdtDef,
};
use rustc_session::Session;
use rustc_target::abi::VariantIdx;

use why3::mlcfg::{BinOp, BlockId, Constant, Exp, Pattern, Statement, Terminator as MlT};

use super::FunctionTranslator;

// Translate the terminator of a basic block.
// There isn't much that's special about this. The only subtlety is in how
// we translate switchInt. We rewrite it into a primitive constructor match
// rather than switching on discriminant since WhyML doesn't have integer
// patterns in match expressions.

impl<'tcx> FunctionTranslator<'_, '_, 'tcx> {
    pub fn translate_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            Goto { target } => self.emit_terminator(mk_goto(*target)),
            SwitchInt { discr, targets, .. } => {
                let real_discr =
                    discriminator_for_switch(&self.body.basic_blocks()[location.block])
                        .map(Operand::Move)
                        .unwrap_or_else(|| discr.clone());

                let discriminant = self.translate_operand(&real_discr);
                let switch = make_switch(
                    self.ctx.sess,
                    self.tcx,
                    terminator.source_info,
                    real_discr.ty(self.body, self.tcx),
                    targets,
                    discriminant,
                );

                self.emit_terminator(switch);
            }
            Abort => self.emit_terminator(MlT::Absurd),
            Return => self.emit_terminator(MlT::Return),
            Unreachable => self.emit_terminator(MlT::Absurd),
            Call { func, args, destination, .. } => {
                let fun_def_id = func_defid(func).expect("expected call with function");

                let mut func_args: Vec<_> =
                    args.iter().map(|arg| self.translate_operand(arg)).collect();

                if func_args.is_empty() {
                    // We use tuple as a dummy argument for 0-ary functions
                    func_args.push(Exp::Tuple(vec![]))
                }
                // TODO: Get functions to be turned into QPaths!
                let call_exp = if self.is_box_new(fun_def_id) {
                    assert_eq!(func_args.len(), 1);

                    func_args.remove(0)
                } else {
                    let fname = match func.ty(self.body, self.tcx).kind() {
                        ty::TyKind::FnDef(defid, _) => super::translate_value_id(self.tcx, *defid),
                        _ => panic!("not a function"),
                    };
                    Exp::Call(box Exp::QVar(fname), func_args)
                };

                if destination.is_none() {
                    // If we have no target block after the call, then we cannot move past it.
                    self.emit_terminator(MlT::Absurd);
                } else {
                    let (loc, bb) = destination.unwrap();
                    self.emit_assignment(&loc, call_exp);
                    self.emit_terminator(MlT::Goto(BlockId(bb.into())));
                }
            }
            Assert { cond, expected, msg: _, target, cleanup: _ } => {
                let mut ass = self.translate_operand(cond);
                if !expected {
                    ass = Exp::UnaryOp(why3::mlcfg::UnOp::Not, box ass);
                }
                self.emit_statement(Statement::Assert(ass));
                self.emit_terminator(mk_goto(*target))
            }

            FalseEdge { real_target, .. } => self.emit_terminator(mk_goto(*real_target)),

            // TODO: Do we really need to do anything more?
            Drop { target, .. } => self.emit_terminator(mk_goto(*target)),
            Resume => {
                log::debug!("Skipping resume terminator");
            }
            FalseUnwind { real_target, .. } => {
                self.emit_terminator(mk_goto(*real_target));
            }
            DropAndReplace { target, place, value, .. } => {
                // Drop
                let ty = place.ty(self.body, self.tcx).ty;
                let pl_exp = self.translate_rplace(&place);
                let assumption: Exp = super::ty::drop_predicate(&mut self.ctx, ty).app_to(pl_exp);
                self.emit_statement(Statement::Assume(assumption));

                // Assign
                let rhs = match value {
                    Operand::Move(pl) | Operand::Copy(pl) => {
                        self.translate_rplace(& pl)
                    }
                    Operand::Constant(box c) => Exp::Const(super::from_mir_constant(self.tcx, c)),
                };

                self.emit_assignment(&place, rhs);

                self.emit_terminator(mk_goto(*target))
            }
            Yield { .. } | GeneratorDrop | InlineAsm { .. } => {
                unreachable!("{:?}", terminator.kind)
            }
        }
    }

    fn is_box_new(&self, def_id: DefId) -> bool {
        self.tcx.def_path_str(def_id) == "std::boxed::Box::<T>::new"
    }
}

// Try to extract a function defid from an operand
fn func_defid(op: &Operand<'_>) -> Option<DefId> {
    let fun_ty = op.constant().unwrap().literal.ty();
    if let ty::TyKind::FnDef(def_id, _) = fun_ty.kind() {
        Some(*def_id)
    } else {
        None
    }
}

use rustc_middle::mir::{BasicBlockData, Place, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{Ty, TyCtxt};

// Find the place being discriminated, if there is one
pub fn discriminator_for_switch<'tcx>(bbd: &BasicBlockData<'tcx>) -> Option<Place<'tcx>> {
    let discr = if let TerminatorKind::SwitchInt { discr, .. } = &bbd.terminator().kind {
        discr
    } else {
        return None;
    };

    if let StatementKind::Assign(box (pl, Rvalue::Discriminant(real_discr))) =
        bbd.statements.last()?.kind
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

pub fn make_switch<'tcx>(
    sess: &Session,
    tcx: TyCtxt<'tcx>,
    si: SourceInfo,
    switch_ty: Ty<'tcx>,
    targets: &SwitchTargets,
    discr: Exp,
) -> MlT {
    use rustc_middle::ty::TyKind::*;
    use Pattern::*;
    match switch_ty.kind() {
        Adt(def, _) => {
            let d_to_var: HashMap<_, _> =
                def.discriminants(tcx).map(|(idx, d)| (d.val, idx)).collect();

            let mut branches: Vec<_> = targets
                .iter()
                .map(|(disc, tgt)| (variant_pattern(tcx, def, d_to_var[&disc]), mk_goto(tgt)))
                .collect();
            branches.push((Wildcard, mk_goto(targets.otherwise())));

            MlT::Switch(discr, branches)
        }
        Bool => {
            let mut branches: Vec<(Pattern, _)> = vec![Pattern::mk_false(), Pattern::mk_true()]
                .into_iter()
                .zip(targets.all_targets().iter().map(|tgt| mk_goto(*tgt)))
                .collect();
            branches.push((Wildcard, mk_goto(targets.otherwise())));
            MlT::Switch(discr, branches)
        }
        Uint(_) => {
            let annoying: Vec<(Constant, MlT)> = targets
                .iter()
                .map(|(val, tgt)| (Constant::Uint(val, None), mk_goto(tgt)))
                .collect();

            let default = mk_goto(targets.otherwise());
            build_constant_switch(discr, annoying.into_iter(), default)
        }
        Int(_) => {
            let annoying: Vec<(Constant, MlT)> = targets
                .iter()
                .map(|(val, tgt)| (Constant::Int(val as i128, None), mk_goto(tgt)))
                .collect();

            let default = mk_goto(targets.otherwise());
            build_constant_switch(discr, annoying.into_iter(), default)
        }
        Float(_) => sess.span_fatal_with_code(
            si.span,
            "Float patterns are currently unsupported",
            DiagnosticId::Error(String::from("creusot")),
        ),
        _ => unimplemented!(),
    }
}

fn mk_goto(bb: rustc_middle::mir::BasicBlock) -> MlT {
    MlT::Goto(BlockId(bb.into()))
}

fn build_constant_switch<T>(discr: Exp, targets: T, default: MlT) -> MlT
where
    T: Iterator<Item = (Constant, MlT)> + DoubleEndedIterator,
{
    targets.rfold(default, |acc, (val, term)| {
        MlT::Switch(
            Exp::BinaryOp(BinOp::Eq, box discr.clone(), box Exp::Const(val)),
            vec![(Pattern::mk_true(), term), (Pattern::mk_false(), acc)],
        )
    })
}

pub fn variant_pattern(tcx: TyCtxt<'_>, def: &AdtDef, vid: VariantIdx) -> Pattern {
    let variant = &def.variants[vid];
    let wilds = variant.fields.iter().map(|_| Pattern::Wildcard).collect();
    let cons_name = super::translate_value_id(tcx, variant.def_id);

    Pattern::ConsP(cons_name, wilds)
}
