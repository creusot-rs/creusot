use super::BodyTranslator;
use crate::{
    ctx::TranslationCtx,
    translation::{
        fmir::{self, Branches, Expr, RValue, Terminator},
        specification::typing::{Term, TermKind, UnOp},
        traits,
    },
    util::is_ghost_closure,
};
use creusot_rustc::{
    hir::def_id::DefId,
    infer::{
        infer::{InferCtxt, TyCtxtInferExt},
        traits::{FulfillmentError, Obligation, ObligationCause, TraitEngine},
    },
    middle::{
        mir::{self, SwitchTargets, TerminatorKind, TerminatorKind::*},
        ty::{
            self,
            subst::{GenericArgKind, SubstsRef},
            ParamEnv, Predicate, Ty, TyKind,
        },
    },
    smir::mir::{
        BasicBlock, BasicBlockData, Location, Operand, Place, Rvalue, SourceInfo, StatementKind,
    },
    span::Span,
    trait_selection::traits::FulfillmentContext,
};
use itertools::Itertools;
use std::collections::HashMap;

// Translate the terminator of a basic block.
// There isn't much that's special about this. The only subtlety is in how
// we translate switchInt. We rewrite it into a primitive constructor match
// rather than switching on discriminant since WhyML doesn't have integer
// patterns in match expressions.

impl<'tcx> BodyTranslator<'_, '_, 'tcx> {
    pub fn translate_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        let span = terminator.source_info.span;
        match &terminator.kind {
            Goto { target } => self.emit_terminator(mk_goto(*target)),
            SwitchInt { discr, targets, .. } => {
                let real_discr =
                    discriminator_for_switch(&self.body.basic_blocks()[location.block])
                        .map(Operand::Move)
                        .unwrap_or_else(|| discr.clone());

                let discriminant = self.translate_operand(&real_discr);
                let switch = make_switch(
                    self.ctx,
                    terminator.source_info,
                    real_discr.ty(self.body, self.tcx),
                    targets,
                    discriminant,
                );

                self.emit_terminator(switch);
            }
            Abort => self.emit_terminator(Terminator::Abort),
            Return => self.emit_terminator(Terminator::Return),
            Unreachable => self.emit_terminator(Terminator::Abort),
            Call { func, args, destination, target, .. } => {
                if target.is_none() {
                    // If we have no target block after the call, then we cannot move past it.
                    self.emit_terminator(Terminator::Abort);
                    return;
                }

                let (fun_def_id, subst) = func_defid(func).expect("expected call with function");

                if let Some(param) = subst.get(0) &&
                    let GenericArgKind::Type(ty) = param.unpack() &&
                    let Some(def_id) = is_ghost_closure(self.tcx, ty) {
                    let assertion = self.assertions.remove(&def_id).unwrap();
                    let (loc, bb) = (destination, target.unwrap());

                    self.emit_ghost_assign(*loc, assertion);
                    self.emit_terminator(Terminator::Goto(bb));
                    return;
                }

                let predicates = self
                    .ctx
                    .extern_spec(fun_def_id)
                    .map(|p| p.predicates_for(self.tcx, subst))
                    .unwrap_or_else(Vec::new);

                use creusot_rustc::trait_selection::traits::error_reporting::InferCtxtExt;
                self.tcx.infer_ctxt().enter(|infcx| {
                    let res =
                        evaluate_additional_predicates(&infcx, predicates, self.param_env(), span);
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
                    func_args.push(Expr::Tuple(vec![]))
                }
                let call_exp = if self.is_box_new(fun_def_id) {
                    assert_eq!(func_args.len(), 1);

                    func_args.remove(0)
                } else {
                    let (fun_def_id, subst) =
                        resolve_function(self.ctx, self.param_env(), fun_def_id, subst, span);

                    let exp = Expr::Call(fun_def_id, subst, func_args);
                    let span = span.source_callsite();
                    Expr::Span(span, box exp)
                };

                let (loc, bb) = (destination, target.unwrap());
                self.emit_assignment(&loc, RValue::Expr(call_exp));
                self.emit_terminator(Terminator::Goto(bb));
            }
            Assert { cond, expected, msg: _, target, cleanup: _ } => {
                let mut ass = match cond {
                    Operand::Copy(pl) | Operand::Move(pl) => {
                        if let Some(locl) = pl.as_local() {
                            Term {
                                kind: TermKind::Var(self.translate_local(locl).symbol()),
                                span,
                                ty: cond.ty(self.body, self.tcx),
                            }
                        } else {
                            unreachable!("assertion contains something other than local")
                        }
                    }
                    Operand::Constant(_) => todo!(),
                };
                if !expected {
                    ass = Term {
                        ty: ass.ty,
                        span: ass.span,
                        kind: TermKind::Unary { op: UnOp::Not, arg: box ass },
                    };
                }
                self.emit_statementf(fmir::Statement::Assertion(ass));
                self.emit_terminator(mk_goto(*target))
            }

            FalseEdge { real_target, .. } => self.emit_terminator(mk_goto(*real_target)),

            // TODO: Do we really need to do anything more?
            Drop { target, .. } => self.emit_terminator(mk_goto(*target)),
            FalseUnwind { real_target, .. } => {
                self.emit_terminator(mk_goto(*real_target));
            }
            DropAndReplace { target, place, value, .. } => {
                // Resolve
                self.emit_statementf(fmir::Statement::Resolve(*place));

                // Assign
                let rhs = self.translate_operand(value);

                self.emit_assignment(place, RValue::Expr(rhs));

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
}

pub fn resolve_function<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
    sp: Span,
) -> (DefId, SubstsRef<'tcx>) {
    if let Some(it) = ctx.opt_associated_item(def_id) {
        if let ty::TraitContainer(id) = it.container {
            let method = traits::resolve_assoc_item_opt(ctx.tcx, param_env, def_id, subst)
                .expect("could not find instance");

            ctx.translate(id);
            ctx.translate(method.0);

            if !method.0.is_local()
                && !ctx.externs.verified(method.0)
                && ctx.extern_spec(method.0).is_none()
                && ctx.extern_spec(def_id).is_none()
            {
                ctx.warn(sp, "calling an external function with no contract will yield an impossible precondition");
            }

            return method;
        }
    }

    if !def_id.is_local() && !(ctx.extern_spec(def_id).is_some() || ctx.externs.verified(def_id)) {
        ctx.warn(
            sp,
            "calling an external function with no contract will yield an impossible precondition",
        );
    }
    ctx.translate(def_id);

    (def_id, subst)
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
    ctx: &TranslationCtx<'_, 'tcx>,
    si: SourceInfo,
    switch_ty: Ty<'tcx>,
    targets: &SwitchTargets,
    discr: Expr<'tcx>,
) -> Terminator<'tcx> {
    match switch_ty.kind() {
        TyKind::Adt(def, _) => {
            let d_to_var: HashMap<_, _> =
                def.discriminants(ctx.tcx).map(|(idx, d)| (d.val, idx)).collect();

            let branches: Vec<_> =
                targets.iter().map(|(disc, tgt)| (d_to_var[&disc], (tgt))).collect();

            Terminator::Switch(discr, Branches::Constructor(*def, branches, targets.otherwise()))
        }
        TyKind::Bool => {
            let branches: (_, _) = targets
                .iter()
                .sorted()
                .map(|tgt| tgt.1)
                .chain(std::iter::once(targets.otherwise()))
                .take(2)
                .collect_tuple()
                .unwrap();

            Terminator::Switch(discr, Branches::Bool(branches.0, branches.1))
        }
        TyKind::Float(_) => {
            ctx.crash_and_error(si.span, "Float patterns are currently unsupported")
        }
        TyKind::Uint(_) => {
            let branches: Vec<(_, BasicBlock)> =
                targets.iter().map(|(val, tgt)| (val, tgt)).collect();
            Terminator::Switch(discr, Branches::Uint(branches, targets.otherwise()))
        }
        TyKind::Int(_) => {
            let branches: Vec<(_, BasicBlock)> =
                targets.iter().map(|(val, tgt)| (val as i128, tgt)).collect();

            Terminator::Switch(discr, Branches::Int(branches, targets.otherwise()))
        }
        _ => unimplemented!(),
    }
}

fn mk_goto<'tcx>(bb: BasicBlock) -> Terminator<'tcx> {
    Terminator::Goto(bb)
}
