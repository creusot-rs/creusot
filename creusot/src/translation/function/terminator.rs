use rustc_infer::{
    infer::{InferCtxt, TyCtxtInferExt},
    traits::{FulfillmentError, Obligation, ObligationCause, TraitEngine},
};
use rustc_middle::ty::{subst::SubstsRef, ParamEnv, Predicate};
use rustc_span::Span;
use rustc_trait_selection::traits::FulfillmentContext;
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

use why3::exp::{BinOp, Constant, Exp, Pattern};
use why3::mlcfg::{BlockId, Statement, Terminator as MlT};
use why3::QName;

use crate::{translation::traits, util::constructor_qname};

use super::BodyTranslator;

// Translate the terminator of a basic block.
// There isn't much that's special about this. The only subtlety is in how
// we translate switchInt. We rewrite it into a primitive constructor match
// rather than switching on discriminant since WhyML doesn't have integer
// patterns in match expressions.

impl<'tcx> BodyTranslator<'_, '_, 'tcx> {
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
                    self.ctx.tcx.sess,
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
                if destination.is_none() {
                    // If we have no target block after the call, then we cannot move past it.
                    self.emit_terminator(MlT::Absurd);
                    return;
                }

                let (fun_def_id, subst) = func_defid(func).expect("expected call with function");

                let predicates = self
                    .ctx
                    .extern_spec(fun_def_id)
                    .map(|p| p.predicates_for(self.tcx, subst))
                    .unwrap_or_else(Vec::new);

                use rustc_trait_selection::traits::error_reporting::InferCtxtExt;
                self.tcx.infer_ctxt().enter(|infcx| {
                    let res = evaluate_additional_predicates(
                        &infcx,
                        predicates,
                        self.param_env(),
                        terminator.source_info.span,
                    );
                    if let Err(errs) = res {
                        let hir_id =
                            self.tcx.hir().local_def_id_to_hir_id(self.def_id.expect_local());
                        let body_id = self.tcx.hir().body_owned_by(hir_id);
                        infcx.report_fulfillment_errors(&errs, Some(body_id), false);
                    }
                });

                let mut func_args: Vec<_> =
                    args.iter().map(|arg| self.translate_operand(arg)).collect();

                if func_args.is_empty() {
                    // We use tuple as a dummy argument for 0-ary functions
                    func_args.push(Exp::Tuple(vec![]))
                }
                let call_exp = if self.is_box_new(fun_def_id) {
                    assert_eq!(func_args.len(), 1);

                    func_args.remove(0)
                } else {
                    let fname = self.get_func_name(fun_def_id, subst, terminator.source_info.span);
                    self.ctx.attach_span(
                        terminator.source_info.span,
                        Exp::Call(box Exp::impure_qvar(fname), func_args),
                    )
                };

                let (loc, bb) = destination.unwrap();
                self.emit_assignment(&loc, call_exp);
                self.emit_terminator(MlT::Goto(BlockId(bb.into())));
            }
            Assert { cond, expected, msg: _, target, cleanup: _ } => {
                let mut ass = self.translate_operand(cond);
                if !expected {
                    ass = Exp::UnaryOp(why3::exp::UnOp::Not, box ass);
                }
                self.emit_statement(Statement::Assert(ass));
                self.emit_terminator(mk_goto(*target))
            }

            FalseEdge { real_target, .. } => self.emit_terminator(mk_goto(*real_target)),

            // TODO: Do we really need to do anything more?
            Drop { target, .. } => self.emit_terminator(mk_goto(*target)),
            FalseUnwind { real_target, .. } => {
                self.emit_terminator(mk_goto(*real_target));
            }
            DropAndReplace { target, place, value, .. } => {
                // Drop
                let ty = place.ty(self.body, self.tcx).ty;
                let pl_exp = self.translate_rplace(place);
                self.resolve_ty(ty).emit(pl_exp, self);

                // Assign
                let rhs = match value {
                    Operand::Move(pl) | Operand::Copy(pl) => self.translate_rplace(pl),
                    Operand::Constant(box c) => crate::constant::from_mir_constant(
                        self.param_env(),
                        self.ctx,
                        self.names,
                        c,
                    ),
                };

                self.emit_assignment(place, rhs);

                self.emit_terminator(mk_goto(*target))
            }
            Yield { .. } | GeneratorDrop | InlineAsm { .. } | Resume => {
                unreachable!("{:?}", terminator.kind)
            }
        }
    }

    fn is_box_new(&self, def_id: DefId) -> bool {
        self.tcx.def_path_str(def_id) == "std::boxed::Box::<T>::new"
    }

    fn get_func_name(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
        sp: rustc_span::Span,
    ) -> QName {
        if let Some(it) = self.tcx.opt_associated_item(def_id) {
            if let ty::TraitContainer(id) = it.container {
                let params = self.param_env();
                let method = traits::resolve_assoc_item_opt(self.tcx, params, def_id, subst)
                    .expect("could not find instance");

                self.ctx.translate(id);
                self.ctx.translate(method.0);

                if !method.0.is_local()
                    && !(self.ctx.extern_spec(method.0).is_some()
                        || self.ctx.externs.verified(method.0))
                {
                    self.ctx.warn(sp, "calling an external function with no contract will yield an impossible precondition");
                }

                return self.names.insert(method.0, method.1).qname(self.tcx, method.0);
            }
        }

        if !def_id.is_local()
            && !(self.ctx.extern_spec(def_id).is_some() || self.ctx.externs.verified(def_id))
        {
            self.ctx.warn(sp, "calling an external function with no contract will yield an impossible precondition");
        }
        self.ctx.translate(def_id);

        self.names.insert(def_id, subst).qname(self.tcx, def_id)
    }
}

// Try to extract a function defid from an operand
fn func_defid<'tcx>(op: &Operand<'tcx>) -> Option<(DefId, SubstsRef<'tcx>)> {
    let fun_ty = op.constant().unwrap().literal.ty();
    if let ty::TyKind::FnDef(def_id, subst) = fun_ty.kind() {
        Some((*def_id, subst))
    } else {
        None
    }
}

fn evaluate_additional_predicates<'tcx>(
    infcx: &InferCtxt<'_, 'tcx>,
    p: Vec<Predicate<'tcx>>,
    param_env: ParamEnv<'tcx>,
    sp: Span,
) -> Result<(), Vec<FulfillmentError<'tcx>>> {
    let mut fulfill_cx = FulfillmentContext::new();
    for predicate in p {
        let cause = ObligationCause::dummy_with_span(sp);
        let obligation = Obligation { cause, param_env, recursion_depth: 0, predicate };
        // holds &= infcx.predicate_may_hold(&obligation);
        fulfill_cx.register_predicate_obligation(&infcx, obligation);
    }
    let errors = fulfill_cx.select_all_or_error(&infcx);
    if !errors.is_empty() {
        return Err(errors);
    } else {
        return Ok(());
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

            let branches: Vec<_> = targets
                .iter()
                .map(|(disc, tgt)| (variant_pattern(tcx, def, d_to_var[&disc]), mk_goto(tgt)))
                .chain(std::iter::once((Wildcard, mk_goto(targets.otherwise()))))
                .take(def.variants().len())
                .collect();

            MlT::Switch(discr, branches)
        }
        Bool => {
            let branches: Vec<_> = targets
                .iter()
                .map(|tgt| {
                    if tgt.0 == 0 {
                        (Pattern::mk_false(), mk_goto(tgt.1))
                    } else {
                        (Pattern::mk_true(), mk_goto(tgt.1))
                    }
                })
                .chain(std::iter::once((Wildcard, mk_goto(targets.otherwise()))))
                .take(2)
                .collect();

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
    let variant = &def.variants()[vid];
    let wilds = variant.fields.iter().map(|_| Pattern::Wildcard).collect();
    let cons_name = constructor_qname(tcx, variant);

    Pattern::ConsP(cons_name, wilds)
}
