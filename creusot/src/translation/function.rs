mod statement;
mod terminator;

use self::terminator::discriminator_for_switch;
use super::specification::PreSignature;
use crate::{
    analysis::NotFinalPlaces,
    backend::ty_inv::is_tyinv_trivial,
    constant::from_mir_constant,
    contracts_items::{
        get_fn_mut_impl_unnest, get_resolve_function, get_resolve_method, is_snapshot_closure,
        is_spec,
    },
    ctx::*,
    extended_location::ExtendedLocation,
    fmir::{self, LocalDecl, LocalDecls, RValue, TrivialInv, inline_pearlite_subst},
    gather_spec_closures::{LoopSpecKind, SpecClosures, corrected_invariant_names_and_locations},
    naming::{name, variable_name},
    pearlite::{Ident, Pattern, Term, TermKind, TermVisitorMut, normalize, super_visit_mut_term},
    resolve::{HasMoveDataExt, Resolver, place_contains_borrow_deref},
    translation::{specification::contract_of, traits},
};
use indexmap::IndexMap;
use rustc_borrowck::consumers::BorrowSet;
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, bit_set::MixedBitSet};
use rustc_middle::{
    mir::{
        self, BasicBlock, Body, Local, Location, Mutability, Operand, Place, PlaceRef, START_BLOCK,
        TerminatorKind, traversal::reverse_postorder,
    },
    ty::{
        BorrowKind, ClosureKind, GenericArg, GenericArgsRef, Ty, TyCtxt, TyKind, TypeVisitableExt,
        TypingEnv, UpvarCapture,
    },
};
use rustc_mir_dataflow::{
    Analysis as _,
    move_paths::{HasMoveData, LookupResult, MoveData, MovePathIndex},
    on_all_children_bits,
};
use rustc_span::{DUMMY_SP, Span, Symbol};
use rustc_target::abi::{FieldIdx, VariantIdx};
use std::{
    collections::{HashMap, HashSet},
    iter::zip,
    ops::FnOnce,
};

/// Translate a function from rustc's MIR to fMIR.
pub(crate) fn fmir<'tcx>(ctx: &TranslationCtx<'tcx>, body_id: BodyId) -> fmir::Body<'tcx> {
    BodyTranslator::with_context(ctx, body_id, |func_translator| func_translator.translate())
}

/// Translate a MIR body (rustc) to FMIR (creusot).
// TODO: Split this into several sub-contexts: Core, Analysis, Results?
struct BodyTranslator<'a, 'tcx> {
    body_id: BodyId,

    body: &'a Body<'tcx>,
    tree: &'a fmir::ScopeTree<'tcx>,

    resolver: Option<Resolver<'a, 'tcx>>,

    move_data: &'a MoveData<'tcx>,

    typing_env: TypingEnv<'tcx>,

    /// Spec / Snapshot variables
    erased_locals: MixedBitSet<Local>,

    /// Current block being generated
    current_block: (Vec<fmir::Statement<'tcx>>, Option<fmir::Terminator<'tcx>>),

    past_blocks: IndexMap<BasicBlock, fmir::Block<'tcx>>,

    // Type translation context
    ctx: &'a TranslationCtx<'tcx>,

    // Fresh BlockId
    fresh_id: usize,

    invariants: IndexMap<BasicBlock, Vec<(LoopSpecKind, Term<'tcx>)>>,
    /// Invariants to translate as assertions.
    invariant_assertions: IndexMap<DefId, (Term<'tcx>, String)>,
    /// Map of the `proof_assert!` blocks to their translated version.
    assertions: IndexMap<DefId, Term<'tcx>>,
    /// Map of the `snapshot!` blocks to their translated version.
    snapshots: IndexMap<DefId, Term<'tcx>>,

    borrows: Option<&'a BorrowSet<'tcx>>,

    // Translated locals: Symbol for debugging and user-facing error messages, and actual unique Ident
    locals: HashMap<Local, (rustc_span::Symbol, Ident)>,

    vars: LocalDecls<'tcx>,
}

/// The translator encountered something it cannot handle.
///
/// This is bubbled up until we have a span to print the error.
#[derive(Debug)]
enum TranslationError {
    /// Dereference of a raw pointer
    PtrDeref,
}

impl TranslationError {
    fn crash(&self, ctx: &TranslationCtx, span: Span) -> ! {
        ctx.crash_and_error(span,  match self {
            TranslationError::PtrDeref => "Dereference of a raw pointer is forbidden in creusot: use `creusot_contracts::ptr_own::PtrOwn` instead",
        })
    }
}

impl<'tcx> HasMoveData<'tcx> for BodyTranslator<'_, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        self.move_data
    }
}

impl<'body, 'tcx> BodyTranslator<'body, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }

    fn with_context<R, F: for<'b> FnOnce(BodyTranslator<'b, 'tcx>) -> R>(
        ctx: &'body TranslationCtx<'tcx>,
        body_id: BodyId,
        f: F,
    ) -> R {
        let tcx = ctx.tcx;
        let body_with_facts = ctx.body_with_facts(body_id.def_id);
        let (body, move_data, resolver, borrows);
        match body_id.promoted {
            None => {
                body = &body_with_facts.body;
                move_data = MoveData::gather_moves(body, tcx, |_| true);
                resolver = Some(Resolver::new(
                    tcx,
                    body,
                    &body_with_facts.borrow_set,
                    &body_with_facts.region_inference_context,
                    &move_data,
                ));
                borrows = Some(&body_with_facts.borrow_set)
            }
            Some(promoted) => {
                body = body_with_facts.promoted.get(promoted).unwrap();
                move_data = MoveData::gather_moves(body, tcx, |_| true);
                resolver = None;
                borrows = None;
            }
        };

        let typing_env = ctx.typing_env(body.source.def_id());
        let mut erased_locals = MixedBitSet::new_empty(body.local_decls.len());

        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if is_spec(tcx, *def_id) || is_snapshot_closure(tcx, *def_id) {
                    erased_locals.insert(local);
                }
            }
        });

        let (vars, locals) = translate_vars(ctx, body, &erased_locals);
        let invariants = corrected_invariant_names_and_locations(ctx, body);
        let SpecClosures { assertions, snapshots } = SpecClosures::collect(ctx, body);
        f(BodyTranslator {
            body,
            body_id,
            resolver,
            move_data: &move_data,
            tree: &fmir::ScopeTree::build(body, ctx.tcx, &locals),
            typing_env,
            locals,
            vars,
            erased_locals,
            current_block: (Vec::new(), None),
            past_blocks: Default::default(),
            ctx,
            fresh_id: body.basic_blocks.len(),
            invariants: invariants.loop_headers,
            invariant_assertions: invariants.assertions,
            assertions,
            snapshots,
            borrows,
        })
    }

    fn translate(mut self) -> fmir::Body<'tcx> {
        self.translate_body();

        let arg_count = self.body.arg_count;

        assert!(self.assertions.is_empty(), "unused assertions");
        assert!(self.snapshots.is_empty(), "unused snapshots");
        assert!(self.invariants.is_empty(), "unused invariants");

        fmir::Body { locals: self.vars, arg_count, blocks: self.past_blocks, fresh: self.fresh_id }
    }

    fn translate_body(&mut self) {
        let mut not_final_places = NotFinalPlaces::new(self.tcx(), self.body)
            .iterate_to_fixpoint(self.tcx(), self.body, None)
            .into_results_cursor(self.body);

        for (bb, bbd) in reverse_postorder(self.body) {
            self.current_block = (vec![], None);
            if bbd.is_cleanup {
                continue;
            }

            if let Some(resolver) = &mut self.resolver
                && bb == START_BLOCK
            {
                let (_, resolved) = resolver
                    .need_resolve_resolved_places_at(ExtendedLocation::Start(Location::START));
                if let Err(err) = self.resolve_places(resolved.clone(), &resolved) {
                    // TODO: what is the appropriate span here?
                    err.crash(self.ctx, self.body.span);
                }
            }

            let mut invariants = Vec::new();
            let mut variant = None;

            let info = *self.body.source_info(bb.start_location());
            let places = self.tree.visible_places(info.scope);
            for (kind, mut body) in self.invariants.shift_remove(&bb).unwrap_or_else(Vec::new) {
                body.subst(inline_pearlite_subst(self.ctx, &places));
                self.check_use_in_logic(&body, bb.start_location());
                match kind {
                    LoopSpecKind::Variant => {
                        if variant.is_some() {
                            self.ctx.crash_and_error(
                                body.span,
                                "Only one variant can be provided for each loop",
                            );
                        }
                        variant = Some(body);
                    }
                    LoopSpecKind::Invariant(expl) => {
                        invariants.push(fmir::Invariant { body, expl });
                    }
                }
            }

            if let Err(err) = self.resolve_places_between_blocks(bb) {
                err.crash(self.ctx, self.basic_block_first_span(bbd))
            }

            let mut loc = bb.start_location();

            for statement in &bbd.statements {
                if let Err(err) = self.translate_statement(&mut not_final_places, statement, loc) {
                    err.crash(self.ctx, statement.source_info.span);
                }
                loc = loc.successor_within_block();
            }
            self.translate_terminator(&mut not_final_places, bbd.terminator(), loc);

            let block = fmir::Block {
                invariants,
                variant,
                stmts: std::mem::take(&mut self.current_block.0),
                terminator: self.current_block.1.take().unwrap(),
            };

            self.past_blocks.insert(bb, block);
        }
    }

    fn typing_env(&self) -> TypingEnv<'tcx> {
        self.ctx.typing_env(self.body_id.def_id())
    }

    fn emit_statement(&mut self, s: fmir::Statement<'tcx>) {
        self.current_block.0.push(s);
    }

    /// These types cannot contain mutable borrows and thus do not need to be resolved.
    fn skip_resolve_type(&self, ty: Ty<'tcx>) -> bool {
        let ty = self.ctx.normalize_erasing_regions(self.typing_env(), ty);
        self.tcx().type_is_copy_modulo_regions(self.typing_env(), ty)
            || !(ty.has_erased_regions() || ty.still_further_specializable())
    }

    fn emit_resolve(&mut self, pl: PlaceRef<'tcx>) -> Result<(), TranslationError> {
        let place_ty = pl.ty(self.body, self.tcx());

        if self.skip_resolve_type(place_ty.ty) {
            return Ok(());
        }
        if let TyKind::Adt(adt_def, subst) = place_ty.ty.kind()
            && let Some(vi) = place_ty.variant_index
            && adt_def
                .variant(vi)
                .fields
                .iter()
                .all(|f| self.skip_resolve_type(f.ty(self.tcx(), subst)))
        {
            return Ok(());
        }

        let p = self.translate_place(pl)?;

        if !is_tyinv_trivial(self.tcx(), self.typing_env(), place_ty.ty) {
            self.emit_statement(fmir::Statement::AssertTyInv { pl: p.clone() });
        }

        if let Some((did, subst)) = resolve_predicate_of(self.ctx, self.typing_env(), place_ty.ty) {
            self.emit_statement(fmir::Statement::Resolve { did, subst, pl: p });
        }
        Ok(())
    }

    fn emit_terminator(&mut self, t: fmir::Terminator<'tcx>) {
        assert!(self.current_block.1.is_none());

        self.current_block.1 = Some(t);
    }

    /// # Parameters
    ///
    /// `is_final` signals that the emitted borrow should be final: see [`NotFinalPlaces`].
    fn emit_borrow(
        &mut self,
        lhs: &Place<'tcx>,
        rhs: &Place<'tcx>,
        is_final: fmir::BorrowKind,
        span: Span,
    ) {
        let p = self.translate_place(rhs.as_ref()).unwrap_or_else(|err| err.crash(self.ctx, span));

        let rhs_ty = rhs.ty(self.body, self.tcx()).ty;
        let triv_inv = if is_tyinv_trivial(self.tcx(), self.typing_env(), rhs_ty) {
            TrivialInv::Trivial
        } else {
            TrivialInv::NonTrivial
        };

        self.emit_assignment(lhs, fmir::RValue::Borrow(is_final, p, triv_inv), span);
    }

    fn emit_snapshot_assign(&mut self, lhs: Place<'tcx>, rhs: Term<'tcx>, span: Span) {
        self.emit_assignment(&lhs, fmir::RValue::Snapshot(rhs), span)
    }

    fn emit_assignment(&mut self, lhs: &Place<'tcx>, rhs: RValue<'tcx>, span: Span) {
        let p = self.translate_place(lhs.as_ref()).unwrap_or_else(|err| err.crash(self.ctx, span));
        self.emit_statement(fmir::Statement::Assignment(p, rhs, span))
    }

    fn resolve_before_assignment(
        &mut self,
        need: MixedBitSet<MovePathIndex>,
        resolved: &MixedBitSet<MovePathIndex>,
        location: Location,
        destination: Place<'tcx>,
    ) -> Result<(), TranslationError> {
        // The assignement may, in theory, modify a variable that needs to be resolved.
        // Hence we resolve before the assignment.
        self.resolve_places(need, resolved)?;

        // We resolve the destination place, if necessary
        match self.move_data().rev_lookup.find(destination.as_ref()) {
            LookupResult::Parent(None) => {
                // for the kind of move data we ask, all the locals should be move paths, so
                // we know we find something here.
                unreachable!()
            }
            LookupResult::Parent(Some(mp)) => {
                let uninit = self.resolver.as_mut().unwrap().uninit_places_before(location);
                // My understanding is that if the destination is not a move path, then it has to
                // be initialized before the assignment.
                assert!(!uninit.contains(mp));
                if !resolved.contains(mp) {
                    // If destination is a reborrow, then mp cannot be in resolved (since
                    // we are writting in it), so we will go through this test.
                    // Otherwise, we resolve only if it is not already resolved.
                    self.emit_resolve(destination.as_ref())?;
                }
            }
            LookupResult::Exact(mp) => {
                // need_before can contain mp or its children if a subplace of destination
                // is reborrowed
                let (need_before, resolved) = self
                    .resolver
                    .as_mut()
                    .unwrap()
                    .need_resolve_resolved_places_at(ExtendedLocation::Mid(location));
                let mut to_resolve = self.empty_bitset();
                on_all_children_bits(self.move_data(), mp, |mp| {
                    if need_before.contains(mp) {
                        to_resolve.insert(mp);
                    }
                });
                self.resolve_places(to_resolve, &resolved)?;
            }
        }
        Ok(())
    }

    // Check if the destination is a zombie:
    // If result place is dead after the assignment, emit resolve
    fn resolve_after_assignment(
        &mut self,
        next_loc: Location,
        destination: Place<'tcx>,
    ) -> Result<(), TranslationError> {
        let live = self.resolver.as_mut().unwrap().live_places_before(next_loc);
        let (_, resolved) = self
            .resolver
            .as_mut()
            .unwrap()
            .need_resolve_resolved_places_at(ExtendedLocation::Start(next_loc));
        let dest = destination.as_ref();
        match self.move_data().rev_lookup.find(dest) {
            LookupResult::Parent(None) => {
                // for the kind of move data we ask, all the locals should be move paths, so
                // we know we find something here.
                unreachable!()
            }
            LookupResult::Parent(Some(mp)) => {
                if !live.contains(mp) {
                    if place_contains_borrow_deref(dest, self.body, self.tcx()) {
                        if resolved.contains(mp) {
                            self.emit_resolve(self.move_data().move_paths[mp].place.as_ref())?;
                        }
                    } else {
                        self.emit_resolve(dest)?;
                    }
                }
            }
            LookupResult::Exact(mp) => {
                let mut to_resolve = self.empty_bitset();
                on_all_children_bits(self.move_data(), mp, |imp| {
                    if !live.contains(imp) {
                        to_resolve.insert(imp);
                    }
                });
                self.resolve_places(to_resolve, &resolved)?;
            }
        }
        Ok(())
    }

    /// Span for the beginning of the basic block: used in diagnostics.
    // TODO: does this even make sense?
    fn basic_block_first_span(&self, bbd: &mir::BasicBlockData) -> Span {
        match bbd.statements.first() {
            Some(s) => s.source_info.span,
            None => match &bbd.terminator {
                Some(t) => t.source_info.span,
                None => self.body.span,
            },
        }
    }

    // Inserts resolves for locals which need resolution after a terminator, or
    // died over the course of a goto or switch
    fn resolve_places_between_blocks(&mut self, bb: BasicBlock) -> Result<(), TranslationError> {
        let Some(resolver) = &mut self.resolver else {
            return Ok(());
        };
        let pred_blocks = &self.body.basic_blocks.predecessors()[bb];

        if pred_blocks.is_empty() {
            return Ok(());
        }

        let mut resolved_between = pred_blocks
            .iter()
            .map(|&pred| resolver.resolved_places_between_blocks(pred, bb))
            .collect::<Vec<_>>();

        for (pred, resolved) in zip(pred_blocks, resolved_between.iter_mut()) {
            // We do not need to resolve move path that we know are inactive
            // because of a preceding switch.

            let bbd = &self.body.basic_blocks[*pred];
            let _: Option<()> = try {
                let discr_pl = discriminator_for_switch(bbd)?;
                let discr_mp = if let LookupResult::Exact(mp) =
                    self.move_data().rev_lookup.find(discr_pl.as_ref())
                {
                    mp
                } else {
                    continue;
                };
                let adt = discr_pl.ty(self.body, self.tcx()).ty.ty_adt_def()?;
                let targets =
                    if let TerminatorKind::SwitchInt { targets, .. } = &bbd.terminator().kind {
                        targets
                    } else {
                        // discriminator_for_switch returned true above
                        unreachable!()
                    };
                if targets.otherwise() == bb {
                    continue;
                }

                let mut inactive_mps = self.empty_bitset();
                // We first insert all the move paths of the discriminator..
                on_all_children_bits(self.move_data(), discr_mp, |mpi| {
                    inactive_mps.insert(mpi);
                });

                // ..and then remove everything which is active in this branch
                let mut discrs = adt.discriminants(self.tcx());
                for discr in targets.iter().filter_map(|(val, tgt)| (tgt == bb).then_some(val)) {
                    let var = discrs.find(|d| d.1.val == discr).unwrap().0;
                    let pl = self.ctx.mk_place_downcast(discr_pl, adt, var);
                    if let LookupResult::Exact(mp) = self.move_data().rev_lookup.find(pl.as_ref()) {
                        on_all_children_bits(self.move_data(), mp, |mpi| {
                            inactive_mps.remove(mpi);
                        })
                    } else {
                        inactive_mps.remove(discr_mp);
                    }
                }

                resolved.0.subtract(&inactive_mps);
            };
        }

        // If we have multiple predecessors (join point) but all of them agree on the deaths, then don't introduce a dedicated block.
        if resolved_between.windows(2).all(|r| r[0] == r[1]) {
            let r = resolved_between.into_iter().next().unwrap();
            return self.resolve_places(r.0, &r.1);
        }

        for (pred, resolved) in zip(pred_blocks, resolved_between) {
            // If no resolves occured in block transition then skip entirely
            if resolved.0.is_empty() {
                continue;
            };

            // Otherwise, we emit the resolves and move them to a stand-alone block.
            self.resolve_places(resolved.0, &resolved.1)?;
            self.emit_terminator(fmir::Terminator::Goto(bb));
            let resolve_block = fmir::Block {
                variant: None,
                invariants: vec![],
                stmts: std::mem::take(&mut self.current_block.0),
                terminator: self.current_block.1.take().unwrap(),
            };

            let resolve_block_id = self.fresh_block_id();
            self.past_blocks.insert(resolve_block_id, resolve_block);
            self.past_blocks.get_mut(pred).unwrap().terminator.retarget(bb, resolve_block_id);
        }
        Ok(())
    }

    fn fresh_block_id(&mut self) -> BasicBlock {
        let id = BasicBlock::from_usize(self.fresh_id);
        self.fresh_id += 1;
        id
    }

    /// We try to coalesce resolutions for places, if possible
    /// TODO: We may actually want to do the opposite: resolve as deeply as possible,
    /// but taking care of type opacity and recursive types.
    // TODO: this returns an error, but this is mostly because I don't know how to get
    // the right spans. If you find a function `MovePathIndex -> Span`, feel free to handle
    // the error in this function.
    fn resolve_places(
        &mut self,
        to_resolve: MixedBitSet<MovePathIndex>,
        resolved: &MixedBitSet<MovePathIndex>,
    ) -> Result<(), TranslationError> {
        let mut to_resolve_full = to_resolve.clone();
        for mp in to_resolve.iter() {
            let mut all_children = true;
            on_all_children_bits(self.move_data(), mp, |imp| {
                if !to_resolve.contains(imp) && !resolved.contains(imp) {
                    all_children = false
                }
            });
            if all_children {
                on_all_children_bits(self.move_data(), mp, |imp| {
                    if mp != imp {
                        to_resolve_full.remove(imp);
                    }
                });
            } else {
                to_resolve_full.remove(mp);
            }
        }

        let mut to_resolve_partial = to_resolve;
        let mut v = vec![];
        for mp in to_resolve_full.iter() {
            on_all_children_bits(self.move_data(), mp, |imp| {
                to_resolve_partial.remove(imp);
            });

            let pl = self.move_data().move_paths[mp].place;
            if !self.erased_locals.contains(pl.local) {
                v.push(pl);
            }
        }

        for mp in to_resolve_partial.iter() {
            let pl = self.move_data().move_paths[mp].place;
            if self.erased_locals.contains(pl.local) {
                continue;
            }
            let ty = pl.ty(&self.body.local_decls, self.tcx());
            let ty = self.ctx.normalize_erasing_regions(self.typing_env, ty);
            let mut insert = |pl: Place<'tcx>| {
                if !matches!(self.move_data().rev_lookup.find(pl.as_ref()), LookupResult::Exact(_))
                {
                    v.push(pl)
                }
            };
            match ty.ty.kind() {
                TyKind::Adt(adt_def, subst) => {
                    if adt_def.is_box() {
                        insert(self.ctx.mk_place_deref(pl));
                    } else if adt_def.is_enum() {
                        if let Some(vid) = ty.variant_index {
                            let var = adt_def.variant(vid);
                            // TODO: honor access rights for these fields.
                            // I.e., we should not resolve private fields.
                            // Problem: it's unclear what to do if we need to resolve a private
                            // field, but not the whole struct/enum
                            for (fi, fd) in var.fields.iter_enumerated() {
                                insert(self.ctx.mk_place_field(pl, fi, fd.ty(self.tcx(), subst)));
                            }
                        } else {
                            for (i, _var) in adt_def.variants().iter().enumerate() {
                                insert(self.ctx.mk_place_downcast(pl, *adt_def, VariantIdx::new(i)))
                            }
                        }
                    } else {
                        let var = adt_def.variant(VariantIdx::new(0));
                        // TODO: idem
                        for (fi, fd) in var.fields.iter_enumerated() {
                            insert(self.ctx.mk_place_field(pl, fi, fd.ty(self.tcx(), subst)));
                        }
                    }
                }

                TyKind::Tuple(tys) => {
                    for (i, ty) in tys.iter().enumerate() {
                        insert(self.ctx.mk_place_field(pl, FieldIdx::new(i), ty));
                    }
                }

                TyKind::Closure(_did, substs) => {
                    for (i, ty) in substs.as_closure().upvar_tys().iter().enumerate() {
                        insert(self.ctx.mk_place_field(pl, FieldIdx::new(i), ty));
                    }
                }

                TyKind::Array(_, _) | TyKind::Slice(_) | TyKind::Pat(_, _) => todo!(),

                TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_)
                | TyKind::Foreign(_)
                | TyKind::Str
                | TyKind::RawPtr(_, _)
                | TyKind::Alias(_, _)
                | TyKind::Param(_)
                | TyKind::Bound(_, _)
                | TyKind::Placeholder(_)
                | TyKind::Infer(_)
                | TyKind::Error(_)
                | TyKind::Ref(_, _, _)
                | TyKind::FnDef(_, _)
                | TyKind::FnPtr(..)
                | TyKind::Dynamic(_, _, _)
                | TyKind::CoroutineClosure(_, _)
                | TyKind::Coroutine(_, _)
                | TyKind::CoroutineWitness(_, _)
                | TyKind::Never
                | TyKind::UnsafeBinder(_) => unreachable!("{}", ty.ty),
            }
        }

        // TODO determine resolution order based on outlives relation?
        v.sort_by_key(|pl| pl.local);
        for pl in v.into_iter().rev() {
            self.emit_resolve(pl.as_ref())?;
        }
        Ok(())
    }

    /// Useful helper to translate an operand
    ///
    /// # Errors
    ///
    /// Will error when trying to dereference a raw pointer.
    fn translate_operand(
        &self,
        operand: &Operand<'tcx>,
    ) -> Result<fmir::Operand<'tcx>, TranslationError> {
        Ok(match operand {
            Operand::Copy(pl) => fmir::Operand::Copy(self.translate_place(pl.as_ref())?),
            Operand::Move(pl) => fmir::Operand::Move(self.translate_place(pl.as_ref())?),
            Operand::Constant(c) => from_mir_constant(self.typing_env(), self.ctx, c),
        })
    }

    /// Useful helper to translate a place
    ///
    /// # Errors
    ///
    /// Will error when trying to dereference a raw pointer.
    fn translate_place(&self, pl: PlaceRef<'tcx>) -> Result<fmir::Place<'tcx>, TranslationError> {
        let projection = pl
            .iter_projections()
            .map(|(p, elem)| {
                Ok(match elem {
                    mir::ProjectionElem::Deref => {
                        if p.ty(self.body, self.tcx()).ty.is_unsafe_ptr() {
                            return Err(TranslationError::PtrDeref);
                        }
                        mir::ProjectionElem::Deref
                    }
                    mir::ProjectionElem::Field(ix, ty) => mir::ProjectionElem::Field(ix, ty),
                    mir::ProjectionElem::Index(l) => mir::ProjectionElem::Index(self.locals[&l].1),
                    mir::ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                        mir::ProjectionElem::ConstantIndex { offset, min_length, from_end }
                    }
                    mir::ProjectionElem::Subslice { from, to, from_end } => {
                        mir::ProjectionElem::Subslice { from, to, from_end }
                    }
                    mir::ProjectionElem::Downcast(s, ix) => mir::ProjectionElem::Downcast(s, ix),
                    mir::ProjectionElem::OpaqueCast(ty) => mir::ProjectionElem::OpaqueCast(ty),
                    mir::ProjectionElem::Subtype(ty) => mir::ProjectionElem::Subtype(ty),
                })
            })
            .collect::<Result<Box<_>, _>>()?;
        Ok(fmir::Place { local: self.locals[&pl.local].1, projections: projection })
    }

    fn check_use_in_logic(&mut self, term: &Term<'tcx>, location: Location) {
        // TODO: We should refine this check to consider places and not only locals
        if let Some(resolver) = &mut self.resolver {
            let mut bad_vars = resolver.frozen_places_before(location);
            let uninit = resolver.uninit_places_before(location);
            bad_vars.union(&uninit);
            let free_vars = term.free_vars();
            for f in bad_vars.iter() {
                if let Some((sym, ident)) = self.move_data().move_paths[f]
                    .place
                    .as_local()
                    .and_then(|l| self.locals.get(&l))
                    && free_vars.contains(ident)
                {
                    let msg = format!("Use of borrowed or uninitialized variable {}", sym.as_str());
                    self.ctx.crash_and_error(term.span, &msg);
                }
            }
        }
    }
}

/// Find a fmir name for each variable in `body`.
///
/// This will skip mir variables that are in `erased_locals`.
///
/// # Returns
/// - The mapping of mir locals to the symbol used in fmir.
/// - Each (unique) fmir symbol is then mapped to the [`LocalDecl`] information of the
///   mir local (the `vars` variable).
fn translate_vars<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &Body<'tcx>,
    erased_locals: &MixedBitSet<Local>,
) -> (LocalDecls<'tcx>, HashMap<Local, (rustc_span::Symbol, Ident)>) {
    let mut vars = LocalDecls::with_capacity(body.local_decls.len());
    let mut locals = HashMap::new();

    use mir::VarDebugInfoContents::Place;

    for (loc, d) in body.local_decls.iter_enumerated() {
        if erased_locals.contains(loc) {
            continue;
        }
        let name = if !d.is_user_variable() {
            format!("_{}", loc.index())
        } else {
            let x = body.var_debug_info.iter().find(|var_info| match var_info.value {
                Place(p) => p.as_local().map(|l| l == loc).unwrap_or(false),
                _ => false,
            });
            let debug_info = x.expect("expected user variable to have name");
            variable_name(debug_info.name.as_str())
        };
        let ident = ctx.fresh(&name);
        locals.insert(loc, (Symbol::intern(&name), ident));
        let is_arg = 0 < loc.index() && loc.index() <= body.arg_count;
        vars.insert(ident, LocalDecl {
            span: d.source_info.span,
            ty: d.ty,
            temp: !d.is_user_variable(),
            arg: is_arg,
        });
    }
    (vars, locals)
}

fn mk_goto<'tcx>(bb: BasicBlock) -> fmir::Terminator<'tcx> {
    fmir::Terminator::Goto(bb)
}

#[derive(Clone, Debug)]
pub(crate) struct ClosureContract<'tcx> {
    pub(crate) precond: Term<'tcx>,
    pub(crate) postcond_once: Option<Term<'tcx>>,
    pub(crate) postcond_mut: Option<Term<'tcx>>,
    pub(crate) postcond: Option<Term<'tcx>>,
    pub(crate) unnest: Option<Term<'tcx>>,
}

impl<'tcx> TranslationCtx<'tcx> {
    pub(crate) fn build_closure_contract(&self, def_id: DefId) -> ClosureContract<'tcx> {
        let TyKind::Closure(_, subst) = self.type_of(def_id).instantiate_identity().kind() else {
            unreachable!()
        };

        let kind = subst.as_closure().kind();

        let PreSignature { contract, inputs, output } = contract_of(self, def_id);

        let span = self.def_span(def_id);

        let arg_ty = Ty::new_tup_from_iter(self.tcx, inputs[1..].iter().map(|&(_, _, ty)| ty));
        let arg_tuple = Term::var(name::args(), arg_ty);

        let arg_pat = Pattern::tuple(
            inputs[1..].iter().map(|&(nm, span, ty)| Pattern::binder_sp(nm, span, ty)),
            arg_ty,
        );

        let env_ty = self.closure_env_ty(
            self.type_of(def_id).instantiate_identity(),
            kind,
            self.lifetimes.re_erased,
        );
        let self_ = Term::var(name::self_(), env_ty);
        let params: Vec<_> = inputs[1..].iter().map(|&(nm, _, ty)| Term::var(nm, ty)).collect();

        let mut precondition = if contract.is_empty() {
            self.inferred_precondition_term(
                def_id,
                subst,
                kind,
                self_.clone(),
                params.clone(),
                span,
            )
        } else {
            contract.requires_conj(self.tcx)
        };

        let postcond = |target_kind| {
            let postcondition = if contract.is_empty() {
                let mut ret_params = params.clone();
                ret_params.push(Term::var(name::result(), output));

                self.inferred_postcondition_term(
                    def_id,
                    subst,
                    kind,
                    target_kind,
                    self_.clone(),
                    ret_params,
                    span,
                )
            } else {
                contract.ensures_conj(self.tcx)
            };

            Term {
                span: postcondition.span,
                kind: TermKind::Let {
                    pattern: arg_pat.clone(),
                    arg: Box::new(arg_tuple.clone()),
                    body: Box::new(postcondition),
                },
                ty: self.types.bool,
            }
        };

        precondition = Term {
            span: precondition.span,
            kind: TermKind::Let {
                pattern: arg_pat.clone(),
                arg: Box::new(arg_tuple.clone()),
                body: Box::new(precondition),
            },
            ty: self.types.bool,
        };

        let env_ty = self
            .closure_env_ty(
                self.type_of(def_id).instantiate_identity(),
                kind,
                self.lifetimes.re_erased,
            )
            .peel_refs();

        let precond = {
            let self_ = Term::var(name::self_(), env_ty);

            // Preconditions are the same for every kind of closure
            let mut subst = closure_capture_subst(self, def_id, subst, false, None, self_.clone());

            let mut precondition = precondition.clone();
            subst.visit_mut_term(&mut precondition);

            precondition
        };

        let mut contracts = ClosureContract {
            precond,
            postcond: None,
            postcond_once: None,
            postcond_mut: None,
            unnest: None,
        };

        if kind.extends(ClosureKind::Fn) {
            let self_ = Term::var(name::self_(), env_ty);
            let mut csubst =
                closure_capture_subst(self, def_id, subst, false, Some(self_.clone()), self_);
            let mut postcondition = postcond(ClosureKind::Fn);
            csubst.visit_mut_term(&mut postcondition);

            contracts.postcond = Some(postcondition);
        }

        if kind.extends(ClosureKind::FnMut) {
            let self_ = Term::var(name::self_(), env_ty);
            let result_state = Term::var(name::result_state(), env_ty);
            let mut csubst = closure_capture_subst(
                self,
                def_id,
                subst,
                false,
                Some(self_.clone()),
                result_state.clone(),
            );

            let mut postcondition = postcond(ClosureKind::FnMut);
            csubst.visit_mut_term(&mut postcondition);

            let args = self.tcx.instantiate_bound_regions_with_erased(
                subst.as_closure().sig().inputs().map_bound(|l| l[0]),
            );

            let unnest_subst = self.mk_args(&[GenericArg::from(args), GenericArg::from(env_ty)]);

            let unnest_id = get_fn_mut_impl_unnest(self.tcx);

            let mut postcondition: Term<'tcx> = postcondition;
            postcondition =
                postcondition.conj(Term::call_no_normalize(self.tcx, unnest_id, unnest_subst, [
                    self_,
                    result_state,
                ]));

            postcondition = normalize(self.tcx, self.typing_env(def_id), postcondition);
            contracts.postcond_mut = Some(postcondition);

            let mut unnest = closure_unnest(self.tcx, def_id, subst);
            unnest = normalize(self.tcx, self.typing_env(def_id), unnest);

            contracts.unnest = Some(unnest);
        }

        // FnOnce
        let self_ = Term::var(name::self_(), env_ty);
        let mut csubst =
            closure_capture_subst(self, def_id, subst, true, Some(self_.clone()), self_);

        let mut postcondition = postcond(ClosureKind::FnOnce);
        csubst.visit_mut_term(&mut postcondition);
        contracts.postcond_once = Some(postcondition);

        contracts
    }

    fn inferred_precondition_term(
        &self,
        item: DefId,
        args: GenericArgsRef<'tcx>,
        kind: ClosureKind,
        closure_env: Term<'tcx>,
        mut closure_args: Vec<Term<'tcx>>,
        span: Span,
    ) -> Term<'tcx> {
        let env_ty = closure_env.ty;
        let bor_self_ident = Ident::fresh_local("bor_self");

        let bor_self = Term::var(
            bor_self_ident,
            Ty::new_ref(self.tcx, self.tcx.lifetimes.re_erased, env_ty, Mutability::Mut),
        );
        // Based on the underlying kind of closure we may need to wrap the call in a quantifier (at least for FnMut ones)
        match kind {
            ClosureKind::Fn | ClosureKind::FnOnce => {
                closure_args.insert(0, closure_env.clone());
                Term {
                    kind: TermKind::Precondition { item, args, params: closure_args.into() },
                    ty: self.types.bool,
                    span,
                }
            }
            ClosureKind::FnMut => {
                closure_args.insert(0, bor_self.clone());
                let base = Term {
                    kind: TermKind::Precondition { item, args, params: closure_args.into() },
                    ty: self.types.bool,
                    span,
                };
                (bor_self.clone().cur().eq(self.tcx, closure_env))
                    .implies(base)
                    .forall((bor_self_ident.into(), env_ty))
            }
        }
    }

    /// Infers the `postcond_kind` version of the postcondition predicate for the provided closure.
    fn inferred_postcondition_term(
        &self,
        item: DefId,
        args: GenericArgsRef<'tcx>,
        closure_kind: ClosureKind,
        postcond_kind: ClosureKind,
        closure_env: Term<'tcx>,
        mut closure_args: Vec<Term<'tcx>>,
        span: Span,
    ) -> Term<'tcx> {
        let env_ty = closure_env.ty;

        match closure_kind {
            ClosureKind::Fn | ClosureKind::FnOnce => {
                closure_args.insert(0, closure_env.clone());
                Term {
                    kind: TermKind::Postcondition { item, args, params: closure_args.into() },
                    ty: self.types.bool,
                    span,
                }
            }
            ClosureKind::FnMut => {
                let bor_self_ident = Ident::fresh_local("bor_self");
                let bor_self = Term::var(bor_self_ident, env_ty);
                closure_args.insert(0, bor_self.clone());

                let mut base = Term {
                    kind: TermKind::Postcondition { item, args, params: closure_args.into() },
                    ty: self.types.bool,
                    span,
                };

                base = base.conj(bor_self.clone().cur().eq(self.tcx, closure_env));
                if postcond_kind == ClosureKind::FnMut {
                    base = base
                        .conj(bor_self.fin().eq(self.tcx, Term::var(name::result_state(), env_ty)))
                }

                base.exists((bor_self_ident.into(), env_ty))
            }
        }
    }
}

pub(crate) fn closure_resolve<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Term<'tcx> {
    assert! {bound.len() == 1};
    let mut resolve = Term::mk_true(ctx.tcx);
    let self_ = Term::var(bound[0], ctx.type_of(def_id).instantiate_identity());
    let csubst = subst.as_closure();
    let typing_env = TypingEnv::non_body_analysis(ctx.tcx, def_id);
    for (ix, ty) in csubst.upvar_tys().iter().enumerate() {
        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self_.clone()), idx: ix.into() },
            span: DUMMY_SP,
        };

        if let Some((id, subst)) = resolve_predicate_of(ctx, typing_env, ty) {
            resolve = Term::call(ctx.tcx, typing_env, id, subst, [proj]).conj(resolve);
        }
    }

    resolve
}

fn closure_unnest<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Term<'tcx> {
    let ty = Ty::new_closure(tcx, def_id, subst);
    let kind = subst.as_closure().kind();
    let env_ty = tcx.closure_env_ty(ty, kind, tcx.lifetimes.re_erased).peel_refs();
    let self_ = Term::var(name::self_(), env_ty);

    let captures =
        tcx.typeck(def_id.expect_local()).closure_min_captures_flattened(def_id.expect_local());

    let mut unnest = Term::mk_true(tcx);

    for (ix, (capture, ty)) in captures.zip(subst.as_closure().upvar_tys()).enumerate() {
        match capture.info.capture_kind {
            // if we captured by value we get no unnesting predicate
            UpvarCapture::ByValue => continue,
            UpvarCapture::ByRef(is_mut) => {
                let acc = |lhs: Term<'tcx>| Term {
                    ty,
                    kind: TermKind::Projection { lhs: Box::new(lhs), idx: ix.into() },
                    span: DUMMY_SP,
                };
                let cur = self_.clone();
                let fin = Term::var(name::future(), env_ty);

                use rustc_middle::ty::BorrowKind;

                let unnest_one = match is_mut {
                    BorrowKind::Immutable => acc(fin).eq(tcx, acc(cur)),
                    _ => acc(fin).fin().eq(tcx, acc(cur).fin()),
                };

                unnest = unnest_one.conj(unnest);
            }
        }
    }

    unnest
}

// Responsible for replacing occurences of captured variables with projections from the closure environment.
// Must also account for the *kind* of capture and the *kind* of closure involved each time.
pub(crate) struct ClosureSubst<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    self_: Term<'tcx>,
    old_self: Option<Term<'tcx>>,
    self_consumed: bool,
    map: IndexMap<Ident, (UpvarCapture, Ty<'tcx>, FieldIdx)>,
    bound: HashSet<Ident>,
    pub use_of_consumed_var_error: Option<Span>,
}

impl<'tcx> ClosureSubst<'_, 'tcx> {
    // TODO: Simplify this logic.
    fn var(&mut self, x: Ident, span: Span) -> Option<Term<'tcx>> {
        let (ck, ty, idx) = *self.map.get(&x)?;

        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self.self_.clone()), idx },
            span: DUMMY_SP,
        };

        match ck {
            UpvarCapture::ByValue => {
                if self.self_consumed {
                    self.use_of_consumed_var_error = Some(span)
                }
                Some(proj)
            }
            UpvarCapture::ByRef(BorrowKind::Mutable | BorrowKind::UniqueImmutable) => {
                if self.self_consumed { Some(proj.fin()) } else { Some(proj.cur()) }
            }
            UpvarCapture::ByRef(BorrowKind::Immutable) => {
                Some(proj.coerce(ty.builtin_deref(false).unwrap()))
            }
        }
    }

    fn old(&self, x: Ident, span: Span) -> Option<Term<'tcx>> {
        let (ck, ty, idx) = *self.map.get(&x)?;

        let old_self = self.old_self.clone().unwrap_or_else(|| {
            self.ctx.fatal_error(span, "Cannot use `old` in a precondition.").emit()
        });

        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(old_self), idx },
            span: DUMMY_SP,
        };

        match ck {
            UpvarCapture::ByValue => Some(proj),
            UpvarCapture::ByRef(_) => Some(proj.cur()),
        }
    }
}

impl<'tcx> TermVisitorMut<'tcx> for ClosureSubst<'_, 'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        match &mut term.kind {
            TermKind::Old { term: box Term { kind: TermKind::Var(x), .. }, .. } => {
                if !self.bound.contains(&x.0) {
                    if let Some(v) = self.old(x.0, term.span) {
                        *term = v;
                    }
                }
            }
            TermKind::Var(x) => {
                if !self.bound.contains(&x.0) {
                    if let Some(v) = self.var(x.0, term.span) {
                        *term = v;
                    }
                }
            }
            TermKind::Quant { binder, .. } => {
                let mut bound = self.bound.clone();
                for (ident, _) in binder {
                    bound.insert(ident.0);
                }
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Match { arms, .. } => {
                let mut bound = self.bound.clone();
                arms.iter().for_each(|arm| arm.0.binds(&mut bound));
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Let { pattern, box arg, box body } => {
                self.visit_mut_term(arg);
                let mut bound = self.bound.clone();
                pattern.binds(&mut bound);
                std::mem::swap(&mut self.bound, &mut bound);
                self.visit_mut_term(body);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Closure { bound: bound_new, box body } => {
                let mut bound = self.bound.clone();
                bound.extend(bound_new.iter().map(|b| b.0.0));
                std::mem::swap(&mut self.bound, &mut bound);
                self.visit_mut_term(body);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            _ => super_visit_mut_term(term, self),
        }
    }
}

pub(crate) fn closure_capture_subst<'a, 'tcx>(
    ctx: &'a TranslationCtx<'tcx>,
    def_id: DefId,
    cs: GenericArgsRef<'tcx>,
    // What kind of substitution we should generate. The same precondition can be used in several ways
    self_consumed: bool,
    old_self: Option<Term<'tcx>>,
    self_: Term<'tcx>,
) -> ClosureSubst<'a, 'tcx> {
    // TODO: looks like dead code
    let mut fun_def_id = def_id;
    while ctx.is_closure_like(fun_def_id) {
        fun_def_id = ctx.parent(fun_def_id);
    }

    let captures = ctx.closure_captures(def_id.expect_local());

    let map = zip(captures, cs.as_closure().upvar_tys())
        .enumerate()
        .map(|(ix, (cap, ty))| {
            use rustc_middle::hir::place::PlaceBase::*;
            let hir_id = match cap.place.base {
                Rvalue => todo!(),
                StaticItem => todo!(),
                Local(hir_id) => hir_id,
                Upvar(upvar_id) => upvar_id.var_path.hir_id,
            };
            (ctx.rename(hir_id), (cap.info.capture_kind, ty, ix.into()))
        })
        .collect();

    ClosureSubst {
        old_self,
        self_,
        self_consumed,
        map,
        bound: Default::default(),
        ctx,
        use_of_consumed_var_error: None,
    }
}

fn resolve_predicate_of<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let trait_meth_id = get_resolve_method(ctx.tcx);
    let substs = ctx.mk_args(&[GenericArg::from(ty)]);

    // Optimization: if we know there is no Resolve instance for this type, then we do not emit
    // a resolve
    if !ty.is_closure()
        && matches!(
            traits::TraitResolved::resolve_item(ctx.tcx, typing_env, trait_meth_id, substs),
            traits::TraitResolved::NoInstance
        )
    {
        return None;
    }

    Some((get_resolve_function(ctx.tcx), substs))
}
