use super::BodyTranslator;
use crate::{
    contracts_items::{is_box_new, is_ghost_deref, is_ghost_deref_mut, is_snap_from_fn},
    ctx::{HasTyCtxt as _, TranslationCtx},
    lints::{CONTRACTLESS_EXTERNAL_FUNCTION, Diagnostics},
    translation::{
        fmir::{self, *},
        pearlite::{Term, TermKind, UnOp},
        traits::{self, TraitResolved},
    },
};
use itertools::Itertools;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir::{
        self, AssertKind, BasicBlockData, Location, Operand, Place, Rvalue, SourceInfo,
        StatementKind, SwitchTargets,
        TerminatorKind::{self, *},
    },
    ty::{GenericArgKind, Ty, TyKind, TypingMode},
};
use rustc_trait_selection::error_reporting::InferCtxtErrorExt;
use std::collections::{HashMap, HashSet};

// Translate the terminator of a basic block.
// There isn't much that's special about this. The only subtlety is in how
// we translate switchInt. We rewrite it into a primitive constructor match
// rather than switching on discriminant since WhyML doesn't have integer
// patterns in match expressions.

impl<'tcx> BodyTranslator<'_, 'tcx> {
    pub fn translate_terminator(&mut self, terminator: &mir::Terminator<'tcx>, loc: Location) {
        let span = terminator.source_info.span;
        self.resolve_at(loc, span);
        self.activate_two_phase(loc, span);
        let mut term = match &terminator.kind {
            Goto { target } => Terminator::Goto(*target),
            SwitchInt { discr, targets, .. } => {
                let real_discr = discriminator_for_switch(&self.body.basic_blocks[loc.block])
                    .map(Operand::Move)
                    .unwrap_or_else(|| discr.clone());

                let discriminant = self.translate_operand(&real_discr, span);
                let ty = real_discr.ty(self.body, self.tcx());
                make_switch(self.ctx, terminator.source_info, ty, targets, discriminant)
            }
            Return => Terminator::Return,
            Unreachable => Terminator::Abort(terminator.source_info.span),
            &Call { ref func, ref args, destination, mut target, fn_span, .. } => {
                let &TyKind::FnDef(fun_def_id, subst) = func.ty(self.body, self.tcx()).kind()
                else {
                    self.fatal_error(fn_span, "unsupported function call type").emit()
                };
                if is_snap_from_fn(self.ctx.tcx, fun_def_id) {
                    let GenericArgKind::Type(ty) = subst.get(1).unwrap().unpack() else {
                        unreachable!()
                    };
                    let TyKind::Closure(def_id, _) = ty.kind() else { unreachable!() };
                    let assertion = self.snapshots.remove(def_id).unwrap();
                    self.emit_snapshot_assign(destination, assertion, span);
                } else {
                    let func_args: Box<[_]> = args
                        .iter()
                        .map(|arg| self.translate_operand(&arg.node, arg.span))
                        .collect();

                    if is_box_new(self.tcx(), fun_def_id) {
                        let [arg] = *func_args.into_array().unwrap();
                        self.emit_assignment(&destination, RValue::Operand(arg), span);
                    } else {
                        let predicates = self
                            .ctx
                            .extern_spec(fun_def_id)
                            .map(|p| p.predicates_for(self.tcx(), subst))
                            .unwrap_or_default();

                        let infcx = self
                            .ctx
                            .infer_ctxt()
                            .ignoring_regions()
                            .build(TypingMode::non_body_analysis());
                        let res = traits::evaluate_additional_predicates(
                            &infcx,
                            predicates,
                            self.typing_env().param_env,
                            span,
                        );
                        if let Err(errs) = res {
                            infcx.err_ctxt().report_fulfillment_errors(errs);
                        }

                        let tr_res = TraitResolved::resolve_item(
                            self.ctx.tcx,
                            self.typing_env(),
                            fun_def_id,
                            subst,
                        );
                        let (fun_def_id, subst) =
                            tr_res.to_opt(fun_def_id, subst).expect("could not find instance");

                        if self.ctx.sig(fun_def_id).contract.extern_no_spec
                            && let Some(lint_root) =
                                self.body.source_info(loc).scope.lint_root(&self.body.source_scopes)
                        {
                            let name = self.ctx.tcx.item_name(fun_def_id);
                            self.ctx.emit_node_span_lint(
                                CONTRACTLESS_EXTERNAL_FUNCTION,
                                lint_root,
                                span,
                                Diagnostics::ContractlessExternalFunction { name, span },
                            );
                        }

                        if self.ctx.sig(fun_def_id).contract.is_requires_false()
                            && !is_ghost_deref(self.tcx(), fun_def_id)
                            && !is_ghost_deref_mut(self.tcx(), fun_def_id)
                            && !matches!(tr_res, TraitResolved::UnknownFound)
                        {
                            target = None
                        } else {
                            let subst =
                                self.ctx.normalize_erasing_regions(self.typing_env(), subst);

                            self.emit_statement(Statement {
                                kind: fmir::StatementKind::Call(
                                    self.translate_place(destination.as_ref(), span),
                                    fun_def_id,
                                    subst,
                                    func_args,
                                ),
                                span: span.source_callsite(),
                            });
                        }
                    }
                }

                if let Some(bb) = target {
                    self.resolve_at(loc.successor_within_block(), span);
                    Terminator::Goto(bb)
                } else {
                    Terminator::Abort(terminator.source_info.span)
                }
            }
            Assert { cond, expected, msg, target, unwind: _ } => {
                let mut cond = match cond {
                    Operand::Copy(pl) | Operand::Move(pl) => {
                        if let Some(locl) = pl.as_local() {
                            Term {
                                // hack
                                kind: TermKind::Var(self.locals[&locl].1.into()),
                                span,
                                ty: cond.ty(self.body, self.tcx()),
                            }
                        } else {
                            unreachable!("assertion contains something other than local")
                        }
                    }
                    Operand::Constant(_) => {
                        self.ctx.dcx().span_bug(span, "assert value is a constant")
                    }
                };
                if !expected {
                    cond = Term {
                        ty: cond.ty,
                        span: cond.span,
                        kind: TermKind::Unary { op: UnOp::Not, arg: Box::new(cond) },
                    };
                }
                let msg = self.get_explanation(msg);
                self.emit_statement(Statement {
                    kind: fmir::StatementKind::Assertion { cond, msg, trusted: false },
                    span,
                });
                Terminator::Goto(*target)
            }
            Drop { target, .. } => Terminator::Goto(*target),

            FalseUnwind { real_target, .. } => Terminator::Goto(*real_target),
            FalseEdge { .. }
            | CoroutineDrop
            | UnwindResume
            | UnwindTerminate { .. }
            | Yield { .. }
            | InlineAsm { .. }
            | TailCall { .. } => unreachable!("{:?}", terminator.kind),
        };
        // Insert blocks of resolve statements and retarget the terminator to those blocks.
        if let Some(mut resolved) = self.body_data.remove_resolved_between_blocks(loc.block) {
            let mut retarget = HashMap::new();
            for target in term.targets_mut() {
                match resolved.remove(target) {
                    Some(resolves) => {
                        let fresh = self.fresh_block_id();
                        retarget.insert(*target, fresh);
                        let mut stmts = Vec::new();
                        resolves.into_iter().for_each(|place| {
                            self.emit_resolve_into(place.as_ref(), span, &mut stmts)
                        });
                        let block = fmir::Block {
                            invariants: vec![],
                            variant: None,
                            stmts,
                            terminator: fmir::Terminator::Goto(*target),
                        };
                        self.retarget_blocks.push((fresh, block));
                        *target = fresh;
                    }
                    // Either the retarget block has already been created (rewrite `*target`), or there wasn't one in the first place (do nothing)
                    None => {
                        if let Some(goto) = retarget.get(target) {
                            *target = *goto;
                        }
                    }
                }
            }
        }
        self.emit_terminator(term)
    }

    fn get_explanation(&mut self, msg: &mir::AssertKind<Operand<'tcx>>) -> String {
        match msg {
            AssertKind::BoundsCheck { len: _, index: _ } => "expl:index in bounds".to_string(),
            AssertKind::Overflow(op, _a, _b) => format!("expl:{op:?} overflow"),
            AssertKind::OverflowNeg(_op) => "expl:negation overflow".to_string(),
            AssertKind::DivisionByZero(_) => "expl:division by zero".to_string(),
            AssertKind::RemainderByZero(_) => "expl:remainder by zero".to_string(),
            _ => unreachable!("Resume assertions"),
        }
    }
}

// Find the place being discriminated, if there is one
pub(crate) fn discriminator_for_switch<'tcx>(bbd: &BasicBlockData<'tcx>) -> Option<Place<'tcx>> {
    let discr = if let TerminatorKind::SwitchInt { discr, .. } = &bbd.terminator().kind {
        discr
    } else {
        return None;
    };

    if let StatementKind::Assign(box (pl, Rvalue::Discriminant(real_discr))) =
        bbd.statements.last()?.kind
    {
        if discr.place() == Some(pl) { Some(real_discr) } else { None }
    } else {
        None
    }
}

fn make_switch<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    si: SourceInfo,
    switch_ty: Ty<'tcx>,
    targets: &SwitchTargets,
    discr: fmir::Operand<'tcx>,
) -> Terminator<'tcx> {
    match switch_ty.kind() {
        TyKind::Adt(def, substs) => {
            let d_to_var: HashMap<_, _> =
                def.discriminants(ctx.tcx).map(|(idx, d)| (d.val, idx)).collect();

            let branches = targets.iter().map(|(disc, tgt)| (d_to_var[&disc], (tgt))).collect();

            let default = if targets.iter().map(|(disc, _)| disc).collect::<HashSet<_>>().len()
                == def.variants().len()
            {
                None
            } else {
                Some(targets.otherwise())
            };

            Terminator::Switch(discr, Branches::Constructor(*def, substs, branches, default))
        }
        TyKind::Bool => {
            let branches: (_, _) = targets
                .iter()
                .sorted()
                .map(|tgt| tgt.1)
                .chain([targets.otherwise()])
                .take(2)
                .collect_tuple()
                .unwrap();

            Terminator::Switch(discr, Branches::Bool(branches.0, branches.1))
        }
        TyKind::Float(_) => {
            ctx.crash_and_error(si.span, "Float patterns are currently unsupported")
        }
        TyKind::Uint(_) => {
            Terminator::Switch(discr, Branches::Uint(targets.iter().collect(), targets.otherwise()))
        }
        TyKind::Int(_) => {
            let branches = targets.iter().map(|(val, tgt)| (val as i128, tgt)).collect();
            Terminator::Switch(discr, Branches::Int(branches, targets.otherwise()))
        }
        ty => ctx.crash_and_error(si.span, &format!("match on {:?} is currently unsupported", ty)),
    }
}
