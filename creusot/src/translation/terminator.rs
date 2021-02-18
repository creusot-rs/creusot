use std::collections::HashMap;

use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BinOp, SourceInfo, SwitchTargets},
    ty::AdtDef,
};
use rustc_middle::{
    mir::{Location, Operand, Terminator, TerminatorKind::*},
    ty,
};
use rustc_resolve::Namespace;
use rustc_session::Session;
use rustc_target::abi::VariantIdx;

use crate::{
    mlcfg::{Constant, Exp, Pattern, Terminator as MlT},
    place::simplify_place,
};

use super::{ty::Ctx, FunctionTranslator};

// Translate the terminator of a basic block.
// There isn't much that's special about this. The only subtlety is in how
// we translate switchInt. We rewrite it into a primitive constructor match
// rather than switching on discriminant since WhyML doesn't have integer
// patterns in match expressions.

impl<'tcx> FunctionTranslator<'_, '_, 'tcx> {
    pub fn translate_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            Goto { target } => self.emit_terminator(MlT::Goto(target.into())),
            SwitchInt { discr, targets, .. } => {
                let real_discr = discriminator_for_switch(&self.body.basic_blocks()[location.block])
                    .map(Operand::Move)
                    .unwrap_or_else(|| discr.clone());

                let discriminant = self.translate_operand(&real_discr);
                let switch = make_switch(
                    self.sess,
                    &mut self.ty_ctx,
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

                let mut func_args: Vec<_> = args.iter().map(|arg| self.translate_operand(arg)).collect();

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
                        ty::TyKind::FnDef(defid, _) => super::translate_defid(self.tcx, *defid, Namespace::ValueNS),
                        _ => panic!("not a function"),
                    };
                    Exp::Call(box Exp::QVar(fname), func_args)
                };

                if destination.is_none() {
                    // If we have no target block after the call, then we cannot move past it.
                    self.emit_terminator(MlT::Absurd);

                } else {
                    let (loc, bb) = destination.unwrap();
                    self.emit_assignment(&simplify_place(self.tcx, self.body, &loc), call_exp);
                    self.emit_terminator(MlT::Goto(bb.into()));
                }
            }
            Assert { cond: _, expected: _, msg: _, target: _, cleanup: _ } => unimplemented!("assert"),

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
fn func_defid(op: &Operand<'_>) -> Option<DefId> {
    let fun_ty = op.constant().unwrap().literal.ty;
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

    if let StatementKind::Assign(box (pl, Rvalue::Discriminant(real_discr))) = bbd.statements.last()?.kind {
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
    ctx: &mut Ctx<'_, 'tcx>,
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
            let d_to_var: HashMap<_, _> = def.discriminants(tcx).map(|(idx, d)| (d.val, idx)).collect();

            let mut branches: Vec<_> = targets
                .iter()
                .map(|(disc, tgt)| (variant_pattern(ctx, def, d_to_var[&disc]), MlT::Goto(tgt.into())))
                .collect();
            branches.push((Wildcard, MlT::Goto(targets.otherwise().into())));

            MlT::Switch(discr, branches)
        }
        Bool => {
            let mut branches: Vec<(Pattern, _)> =
                vec![Pattern::mk_false(), Pattern::mk_true()]
                    .into_iter()
                    .zip(targets.all_targets().iter().map(|tgt| MlT::Goto(tgt.into())))
                    .collect();
            branches.push((Wildcard, MlT::Goto(targets.otherwise().into())));
            MlT::Switch(discr, branches)
        }
        Uint(_) => {
            let annoying: Vec<(Constant, MlT)> =
                targets.iter().map(|(val, tgt)| (Constant::Uint(val), MlT::Goto(tgt.into()))).collect();

            let default = MlT::Goto(targets.otherwise().into());
            build_constant_switch(discr, annoying.into_iter(), default)
        }
        Int(_) => {
            let annoying: Vec<(Constant, MlT)> =
                targets.iter().map(|(val, tgt)| (Constant::Int(val as i128), MlT::Goto(tgt.into()))).collect();

            let default = MlT::Goto(targets.otherwise().into());
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

fn build_constant_switch<T>(discr: Exp, targets: T, default: MlT) -> MlT
where
    T: Iterator<Item = (Constant, MlT)> + DoubleEndedIterator,
{
    targets.rfold(default, |acc, (val, term)| {
        MlT::Switch(
            Exp::BinaryOp(BinOp::Eq.into(), box discr.clone(), box Exp::Const(val)),
            vec![(Pattern::mk_true(), term), (Pattern::mk_false(), acc)],
        )
    })
}

pub fn variant_pattern(ctx: &mut Ctx<'_, '_>, def: &AdtDef, vid: VariantIdx) -> Pattern {
    let variant = &def.variants[vid];
    let wilds = variant.fields.iter().map(|_| Pattern::Wildcard).collect();
    let mut cons_name = super::ty::translate_ty_name(ctx, def.did);
    cons_name.make_constructor(variant.ident.to_string());

    Pattern::ConsP(cons_name, wilds)
}
