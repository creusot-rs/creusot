use super::BodyTranslator;
use crate::{
    analysis::NotFinalPlaces,
    contracts_items::{is_box_new, is_snap_from_fn},
    ctx::TranslationCtx,
    extended_location::ExtendedLocation,
    lints::contractless_external_function::{
        CONTRACTLESS_EXTERNAL_FUNCTION, ContractlessExternalFunction,
    },
    resolve::HasMoveDataExt,
    translation::{
        fmir::{self, *},
        pearlite::{Term, TermKind, UnOp},
        traits::{self, TraitResolved},
    },
};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir::{
        self, AssertKind, BasicBlockData, Local, Location, Operand, Place, Rvalue, SourceInfo,
        StatementKind, SwitchTargets,
        TerminatorKind::{self, *},
    },
    ty::{self, GenericArgKind, GenericArgsRef, Ty, TyKind, TypingEnv, TypingMode},
};
use rustc_mir_dataflow::{
    ResultsCursor,
    move_paths::{HasMoveData, LookupResult},
    on_all_children_bits,
};
use rustc_span::Span;
use rustc_trait_selection::error_reporting::InferCtxtErrorExt;
use std::collections::{HashMap, HashSet};

// Translate the terminator of a basic block.
// There isn't much that's special about this. The only subtlety is in how
// we translate switchInt. We rewrite it into a primitive constructor match
// rather than switching on discriminant since WhyML doesn't have integer
// patterns in match expressions.

impl<'tcx> BodyTranslator<'_, 'tcx> {
    pub fn translate_terminator(
        &mut self,
        not_final_borrows: &mut ResultsCursor<'_, 'tcx, NotFinalPlaces<'tcx>>,
        terminator: &mir::Terminator<'tcx>,
        location: Location,
    ) {
        let span = terminator.source_info.span;
        self.activate_two_phase(not_final_borrows, location, span);
        let mut resolved_during = self
            .resolver
            .as_mut()
            .map(|r| r.resolved_places_during(ExtendedLocation::End(location)));
        let term;
        match &terminator.kind {
            Goto { target } => term = Terminator::Goto(*target),
            SwitchInt { discr, targets, .. } => {
                let real_discr = discriminator_for_switch(&self.body.basic_blocks[location.block])
                    .map(Operand::Move)
                    .unwrap_or_else(|| discr.clone());

                let discriminant = self
                    .translate_operand(&real_discr)
                    .unwrap_or_else(|err| err.crash(self.ctx, terminator.source_info.span));
                let ty = real_discr.ty(self.body, self.tcx());
                let switch =
                    make_switch(self.ctx, terminator.source_info, ty, targets, discriminant);
                term = switch;
            }
            Return => {
                if let Some(resolver) = &mut self.resolver {
                    let (mut need, resolved) =
                        resolver.need_resolve_resolved_places_at(ExtendedLocation::Start(location));
                    // do not resolve return local
                    for mp in need.clone().iter() {
                        if self.move_data().base_local(mp) == Local::from_usize(0) {
                            need.remove(mp);
                        }
                    }
                    if let Err(err) = self.resolve_places(need, &resolved) {
                        err.crash(self.ctx, span)
                    }
                    resolved_during = None;
                }

                term = Terminator::Return
            }
            Unreachable => term = Terminator::Abort(terminator.source_info.span),
            &Call { ref func, ref args, destination, mut target, fn_span, .. } => {
                let Some((fun_def_id, subst)) = func_defid(func) else {
                    self.ctx.fatal_error(fn_span, "unsupported function call type").emit()
                };
                if let Some((need, resolved)) = resolved_during.take() {
                    if let Err(err) =
                        self.resolve_before_assignment(need, &resolved, location, destination)
                    {
                        err.crash(self.ctx, span)
                    }
                }

                if is_snap_from_fn(self.ctx.tcx, fun_def_id) {
                    let GenericArgKind::Type(ty) = subst.get(1).unwrap().unpack() else {
                        unreachable!()
                    };
                    let TyKind::Closure(def_id, _) = ty.kind() else { unreachable!() };
                    let mut assertion = self.snapshots.shift_remove(def_id).unwrap();
                    let places = self.tree.visible_places(terminator.source_info.scope);
                    assertion.subst(inline_pearlite_subst(self.ctx, &places));
                    self.check_use_in_logic(&assertion, location);
                    self.emit_snapshot_assign(destination, assertion, span);
                } else {
                    let func_args: Box<[_]> = args
                        .iter()
                        .map(|arg| {
                            self.translate_operand(&arg.node)
                                .unwrap_or_else(|err| err.crash(self.ctx, arg.span))
                        })
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

                        let (fun_def_id, subst) = resolve_function(
                            self.ctx,
                            self.typing_env(),
                            fun_def_id,
                            subst,
                            (self.body, span, location),
                        );

                        if self.ctx.sig(fun_def_id).contract.is_requires_false() {
                            target = None
                        } else {
                            let subst =
                                self.ctx.normalize_erasing_regions(self.typing_env(), subst);

                            self.emit_statement(Statement {
                                kind: fmir::StatementKind::Call(
                                    self.translate_place(destination.as_ref())
                                        .unwrap_or_else(|err| err.crash(self.ctx, span)),
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
                    if self.resolver.is_some() {
                        if let Err(err) = self
                            .resolve_after_assignment(target.unwrap().start_location(), destination)
                        {
                            err.crash(self.ctx, span)
                        }
                    }

                    term = Terminator::Goto(bb);
                } else {
                    term = Terminator::Abort(terminator.source_info.span);
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
                term = Terminator::Goto(*target)
            }
            Drop { target, place, .. } => {
                if self.resolver.is_some() {
                    // place may need to be resolved since it may be frozen.
                    if let LookupResult::Exact(mp) =
                        self.move_data().rev_lookup.find(place.as_ref())
                    {
                        let (need_start, resolved) = self
                            .resolver
                            .as_mut()
                            .unwrap()
                            .need_resolve_resolved_places_at(ExtendedLocation::Start(location));
                        let mut to_resolve = self.empty_bitset();
                        on_all_children_bits(self.move_data(), mp, |mpi| {
                            if need_start.contains(mpi) {
                                to_resolve.insert(mpi);
                            }
                        });
                        if let Err(err) = self.resolve_places(to_resolve, &resolved) {
                            err.crash(self.ctx, span)
                        }
                    } else {
                        // If the place we drop is not a move path, then the MaybeUninit analysis ignores it. So we do not miss a resolve.
                    }
                }

                term = Terminator::Goto(*target)
            }

            FalseUnwind { real_target, .. } => term = Terminator::Goto(*real_target),
            FalseEdge { .. }
            | CoroutineDrop
            | UnwindResume
            | UnwindTerminate { .. }
            | Yield { .. }
            | InlineAsm { .. }
            | TailCall { .. } => unreachable!("{:?}", terminator.kind),
        }
        if let Some((need, resolved)) = resolved_during {
            if let Err(err) = self.resolve_places(need, &resolved) {
                err.crash(self.ctx, span)
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

/// # Parameters
///
/// - `report_location`: used to emit an eventual warning.
fn resolve_function<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
    report_location: (&mir::Body<'tcx>, Span, Location),
) -> (DefId, GenericArgsRef<'tcx>) {
    let res = if ctx.trait_of_item(def_id).is_some() {
        TraitResolved::resolve_item(ctx.tcx, typing_env, def_id, subst)
            .to_opt(def_id, subst)
            .expect("could not find instance")
    } else {
        (def_id, subst)
    };

    if ctx.sig(res.0).contract.extern_no_spec {
        let (body, span, location) = report_location;
        let name = ctx.tcx.item_name(def_id);
        let source_info = body.source_info(location);
        if let Some(lint_root) = source_info.scope.lint_root(&body.source_scopes) {
            ctx.emit_node_span_lint(
                CONTRACTLESS_EXTERNAL_FUNCTION,
                lint_root,
                span,
                ContractlessExternalFunction { name, span },
            );
        }
    }

    res
}

// Try to extract a function defid from an operand
fn func_defid<'tcx>(op: &Operand<'tcx>) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let fun_ty = op.constant()?.const_.ty();
    if let ty::TyKind::FnDef(def_id, subst) = fun_ty.kind() { Some((*def_id, subst)) } else { None }
}

// Find the place being discriminated, if there is one
pub(super) fn discriminator_for_switch<'tcx>(bbd: &BasicBlockData<'tcx>) -> Option<Place<'tcx>> {
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
