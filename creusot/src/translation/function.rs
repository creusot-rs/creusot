use crate::{
    analysis::NotFinalPlaces,
    backend::ty_inv::is_tyinv_trivial,
    constant::from_mir_constant,
    contracts_items::{
        get_fn_mut_unnest, get_resolve_function, get_resolve_method, is_ghost_closure,
        is_snapshot_closure, is_spec,
    },
    ctx::*,
    extended_location::ExtendedLocation,
    fmir::{self, LocalDecl, LocalDecls, LocalIdent, RValue, TrivialInv},
    gather_spec_closures::{corrected_invariant_names_and_locations, LoopSpecKind, SpecClosures},
    naming::anonymous_param_symbol,
    pearlite::{normalize, Term},
    resolve::{place_contains_borrow_deref, HasMoveDataExt, Resolver},
    translation::{
        pearlite::{self, super_visit_mut_term, TermKind, TermVisitorMut},
        specification::{contract_of, inv_subst, PreContract, PreSignature},
        traits,
    },
};
use indexmap::IndexMap;
use rustc_borrowck::borrow_set::BorrowSet;
use rustc_hir::def_id::DefId;
use rustc_index::{bit_set::BitSet, Idx};
use rustc_middle::{
    mir::{
        self, traversal::reverse_postorder, BasicBlock, Body, Local, Location, Operand, Place,
        PlaceRef, TerminatorKind, START_BLOCK,
    },
    ty::{
        BorrowKind, ClosureKind::*, EarlyBinder, GenericArg, GenericArgsRef, ParamEnv, Ty, TyCtxt,
        TyKind, TypeVisitableExt, UpvarCapture,
    },
};
use rustc_mir_dataflow::{
    move_paths::{HasMoveData, LookupResult, MoveData, MovePathIndex},
    on_all_children_bits, Analysis as _, MoveDataParamEnv,
};
use rustc_span::{Span, Symbol, DUMMY_SP};
use rustc_target::abi::{FieldIdx, VariantIdx};
use rustc_type_ir::ClosureKind;
use std::{
    collections::{HashMap, HashSet},
    iter,
    ops::FnOnce,
};

mod statement;
mod terminator;
use terminator::discriminator_for_switch;

/// Translate a function from rustc's MIR to fMIR.
pub(crate) fn fmir<'tcx>(ctx: &mut TranslationCtx<'tcx>, body_id: BodyId) -> fmir::Body<'tcx> {
    let body = ctx.body(body_id).clone();
    BodyTranslator::with_context(ctx, &body, body_id, |func_translator| func_translator.translate())
}

/// Translate a MIR body (rustc) to FMIR (creusot).
// TODO: Split this into several sub-contexts: Core, Analysis, Results?
struct BodyTranslator<'a, 'tcx> {
    body_id: BodyId,

    body: &'a Body<'tcx>,

    resolver: Option<Resolver<'a, 'tcx>>,

    mdpe: &'a MoveDataParamEnv<'tcx>,

    /// Spec / Snapshot variables
    erased_locals: BitSet<Local>,

    /// Current block being generated
    current_block: (Vec<fmir::Statement<'tcx>>, Option<fmir::Terminator<'tcx>>),

    past_blocks: IndexMap<BasicBlock, fmir::Block<'tcx>>,

    // Type translation context
    ctx: &'a mut TranslationCtx<'tcx>,

    // Fresh BlockId
    fresh_id: usize,

    invariants: IndexMap<BasicBlock, Vec<(LoopSpecKind, Term<'tcx>)>>,

    /// Map of the `proof_assert!` blocks to their translated version.
    assertions: IndexMap<DefId, Term<'tcx>>,
    /// Map of the `snapshot!` blocks to their translated version.
    snapshots: IndexMap<DefId, Term<'tcx>>,
    /// Indicate that the current function is a `ghost!` closure.
    is_ghost_closure: bool,

    borrows: Option<&'a BorrowSet<'tcx>>,

    // Translated locals
    locals: HashMap<Local, Symbol>,

    vars: LocalDecls<'tcx>,
}

impl<'a, 'tcx> HasMoveData<'tcx> for BodyTranslator<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.mdpe.move_data
    }
}

impl<'body, 'tcx> BodyTranslator<'body, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }

    fn with_context<R, F: for<'b> FnOnce(BodyTranslator<'b, 'tcx>) -> R>(
        ctx: &'body mut TranslationCtx<'tcx>,
        body: &'body Body<'tcx>,
        body_id: BodyId,
        f: F,
    ) -> R {
        let tcx = ctx.tcx;
        let param_env = tcx.param_env(body.source.def_id());
        let move_data = MoveData::gather_moves(body, tcx, param_env, |_| true);
        let mdpe = &MoveDataParamEnv { move_data, param_env };

        let invariants = corrected_invariant_names_and_locations(ctx, &body);
        let SpecClosures { assertions, snapshots } = SpecClosures::collect(ctx, &body);
        let mut erased_locals = BitSet::new_empty(body.local_decls.len());

        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if is_spec(tcx, *def_id) || is_snapshot_closure(tcx, *def_id) {
                    erased_locals.insert(local);
                }
            }
        });

        let bor;
        let (resolver, borrows) = match body_id.promoted {
            None => {
                let with_facts = ctx.body_with_facts(body_id.def_id);
                bor = with_facts.borrow_set.clone();
                let borrows = bor.as_ref();
                #[allow(unused_mut)]
                let mut resolver = Resolver::new(
                    tcx,
                    body,
                    borrows,
                    with_facts.region_inference_context.clone(),
                    mdpe,
                );
                // eprintln!("--------------- {:?}", body_id);
                // eprintln!("{:?}", mdpe.move_data);
                // resolver.debug();
                (Some(resolver), Some(borrows))
            }
            Some(_) => (None, None),
        };

        let (vars, locals) = translate_vars(&body, &erased_locals);

        f(BodyTranslator {
            body,
            body_id,
            resolver,
            mdpe,
            locals,
            vars,
            erased_locals,
            current_block: (Vec::new(), None),
            past_blocks: Default::default(),
            ctx,
            fresh_id: body.basic_blocks.len(),
            invariants,
            assertions,
            snapshots,
            is_ghost_closure: is_ghost_closure(tcx, body_id.def_id()),
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
            .into_engine(self.tcx(), self.body)
            .iterate_to_fixpoint()
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
                self.resolve_places(resolved.clone(), &resolved);
            }

            let mut invariants = Vec::new();
            let mut variant = None;

            for (kind, mut body) in self.invariants.remove(&bb).unwrap_or_else(Vec::new) {
                body.subst(&inv_subst(
                    self.tcx(),
                    self.body,
                    &self.locals,
                    *self.body.source_info(bb.start_location()),
                ));
                self.check_frozen_in_logic(&body, bb.start_location());
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
                    LoopSpecKind::Invariant => {
                        invariants.push(body);
                    }
                }
            }

            self.resolve_places_between_blocks(bb);

            let mut loc = bb.start_location();

            for statement in &bbd.statements {
                self.translate_statement(&mut not_final_places, statement, loc);
                loc = loc.successor_within_block();
            }

            self.translate_terminator(bbd.terminator(), loc);

            let block = fmir::Block {
                invariants,
                variant,
                stmts: std::mem::take(&mut self.current_block.0),
                terminator: std::mem::replace(&mut self.current_block.1, None).unwrap(),
            };

            self.past_blocks.insert(bb, block);
        }
    }

    fn param_env(&self) -> ParamEnv<'tcx> {
        self.ctx.param_env(self.body_id.def_id())
    }

    fn emit_statement(&mut self, s: fmir::Statement<'tcx>) {
        self.current_block.0.push(s);
    }

    /// These types cannot contain mutable borrows and thus do not need to be resolved.
    fn skip_resolve_type(&self, ty: Ty<'tcx>) -> bool {
        let ty = self.ctx.normalize_erasing_regions(self.param_env(), ty);
        ty.is_copy_modulo_regions(self.tcx(), self.param_env())
            || !(ty.has_erased_regions() || ty.still_further_specializable())
    }

    fn emit_resolve(&mut self, pl: PlaceRef<'tcx>) {
        let place_ty = pl.ty(self.body, self.tcx());

        if self.skip_resolve_type(place_ty.ty) {
            return;
        }
        if let TyKind::Adt(adt_def, subst) = place_ty.ty.kind()
            && let Some(vi) = place_ty.variant_index
            && adt_def
                .variant(vi)
                .fields
                .iter()
                .all(|f| self.skip_resolve_type(f.ty(self.tcx(), subst)))
        {
            return;
        }

        let p = self.translate_place(pl);

        if !is_tyinv_trivial(self.tcx(), self.param_env(), place_ty.ty) {
            self.emit_statement(fmir::Statement::AssertTyInv { pl: p.clone() });
        }

        if let Some((did, subst)) = resolve_predicate_of(self.ctx, self.param_env(), place_ty.ty) {
            self.emit_statement(fmir::Statement::Resolve { did, subst, pl: p });
        }
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
        is_final: Option<usize>,
        span: Span,
    ) {
        let p = self.translate_place(rhs.as_ref());

        let rhs_ty = rhs.ty(self.body, self.tcx()).ty;
        let triv_inv = if is_tyinv_trivial(self.tcx(), self.param_env(), rhs_ty) {
            TrivialInv::Trivial
        } else {
            TrivialInv::NonTrivial
        };

        self.emit_assignment(
            lhs,
            if let Some(deref_index) = is_final {
                fmir::RValue::Borrow(fmir::BorrowKind::Final(deref_index), p, triv_inv)
            } else {
                fmir::RValue::Borrow(fmir::BorrowKind::Mut, p, triv_inv)
            },
            span,
        );
    }

    fn emit_ghost_assign(&mut self, lhs: Place<'tcx>, rhs: Term<'tcx>, span: Span) {
        self.emit_assignment(&lhs, fmir::RValue::Ghost(rhs), span)
    }

    fn emit_assignment(&mut self, lhs: &Place<'tcx>, rhs: RValue<'tcx>, span: Span) {
        let p = self.translate_place(lhs.as_ref());
        self.emit_statement(fmir::Statement::Assignment(p, rhs, span));
    }

    fn resolve_before_assignment(
        &mut self,
        need: BitSet<MovePathIndex>,
        resolved: &BitSet<MovePathIndex>,
        location: Location,
        destination: Place<'tcx>,
    ) {
        // The assignement may, in theory, modify a variable that needs to be resolved.
        // Hence we resolve before the assignment.
        self.resolve_places(need, &resolved);

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
                    self.emit_resolve(destination.as_ref());
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
                self.resolve_places(to_resolve, &resolved);
            }
        }
    }

    // Check if the destination is a zombie:
    // If result place is dead after the assignment, emit resolve
    fn resolve_after_assignment(&mut self, next_loc: Location, destination: Place<'tcx>) {
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
                            self.emit_resolve(self.move_data().move_paths[mp].place.as_ref());
                        }
                    } else {
                        self.emit_resolve(dest)
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
                self.resolve_places(to_resolve, &resolved);
            }
        }
    }

    // Inserts resolves for locals which need resolution after a terminator, or
    // died over the course of a goto or switch
    fn resolve_places_between_blocks(&mut self, bb: BasicBlock) {
        let Some(resolver) = &mut self.resolver else {
            return;
        };
        let pred_blocks = &self.body.basic_blocks.predecessors()[bb];

        if pred_blocks.is_empty() {
            return;
        }

        let mut resolved_between = pred_blocks
            .iter()
            .map(|&pred| resolver.resolved_places_between_blocks(pred, bb))
            .collect::<Vec<_>>();

        for (pred, resolved) in iter::zip(pred_blocks, resolved_between.iter_mut()) {
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
            self.resolve_places(r.0, &r.1);
            return;
        }

        for (pred, resolved) in iter::zip(pred_blocks, resolved_between) {
            // If no resolves occured in block transition then skip entirely
            if resolved.0.count() == 0 {
                continue;
            };

            // Otherwise, we emit the resolves and move them to a stand-alone block.
            self.resolve_places(resolved.0, &resolved.1);
            self.emit_terminator(fmir::Terminator::Goto(bb));
            let resolve_block = fmir::Block {
                variant: None,
                invariants: Vec::new(),
                stmts: std::mem::take(&mut self.current_block.0),
                terminator: std::mem::replace(&mut self.current_block.1, None).unwrap(),
            };

            let resolve_block_id = self.fresh_block_id();
            self.past_blocks.insert(resolve_block_id, resolve_block);
            self.past_blocks.get_mut(pred).unwrap().terminator.retarget(bb, resolve_block_id);
        }
    }

    fn fresh_block_id(&mut self) -> BasicBlock {
        let id = BasicBlock::from_usize(self.fresh_id);
        self.fresh_id += 1;
        id
    }

    /// We try to coalesce resolutions for places, if possible
    /// TODO: We may actually want to do the opposite: resolve as deeply as possible,
    /// but taking care of type opacity and recursive types.
    fn resolve_places(
        &mut self,
        to_resolve: BitSet<MovePathIndex>,
        resolved: &BitSet<MovePathIndex>,
    ) {
        let mut to_resolve_full = to_resolve.clone();
        for mp in to_resolve.iter() {
            let mut all_children = true;
            on_all_children_bits(&self.move_data(), mp, |imp| {
                if !to_resolve.contains(imp) && !resolved.contains(imp) {
                    all_children = false
                }
            });
            if all_children {
                on_all_children_bits(&self.move_data(), mp, |imp| {
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
            on_all_children_bits(&self.move_data(), mp, |imp| {
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
            let ty = self.ctx.normalize_erasing_regions(self.mdpe.param_env, ty);
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
                | TyKind::FnPtr(_)
                | TyKind::Dynamic(_, _, _)
                | TyKind::CoroutineClosure(_, _)
                | TyKind::Coroutine(_, _)
                | TyKind::CoroutineWitness(_, _)
                | TyKind::Never => unreachable!("{}", ty.ty),
            }
        }

        // TODO determine resolution order based on outlives relation?
        v.sort_by_key(|pl| pl.local);
        for pl in v.into_iter().rev() {
            self.emit_resolve(pl.as_ref())
        }
    }

    // Useful helper to translate an operand
    fn translate_operand(&self, operand: &Operand<'tcx>) -> fmir::Operand<'tcx> {
        let kind = match operand {
            Operand::Copy(pl) => fmir::Operand::Copy(self.translate_place(pl.as_ref())),
            Operand::Move(pl) => fmir::Operand::Move(self.translate_place(pl.as_ref())),
            Operand::Constant(c) => from_mir_constant(self.param_env(), self.ctx, c),
        };
        kind
    }

    fn translate_place(&self, pl: PlaceRef<'tcx>) -> fmir::Place<'tcx> {
        let projection = pl
            .projection
            .into_iter()
            .map(|p| match *p {
                mir::ProjectionElem::Deref => mir::ProjectionElem::Deref,
                mir::ProjectionElem::Field(ix, ty) => mir::ProjectionElem::Field(ix, ty),
                mir::ProjectionElem::Index(l) => mir::ProjectionElem::Index(self.locals[&l]),
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
            .collect();
        fmir::Place { local: self.locals[&pl.local], projection }
    }

    fn check_frozen_in_logic(&mut self, term: &Term<'tcx>, location: Location) {
        // TODO: We should refine this check to consider places and not only locals
        if let Some(resolver) = &mut self.resolver {
            let frozen = resolver.frozen_places_before(location);
            let free_vars = term.free_vars();
            for f in frozen.iter() {
                if let Some(l) =
                    self.move_data().move_paths[f].place.as_local().map(|l| self.locals[&l])
                    && free_vars.contains(&l)
                {
                    let msg = format!("Use of borrowed variable {}", l);
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
    body: &Body<'tcx>,
    erased_locals: &BitSet<Local>,
) -> (LocalDecls<'tcx>, HashMap<Local, Symbol>) {
    let mut vars = LocalDecls::with_capacity(body.local_decls.len());
    let mut locals = HashMap::new();

    use mir::VarDebugInfoContents::Place;

    let mut names = HashMap::new();
    for (loc, d) in body.local_decls.iter_enumerated() {
        if erased_locals.contains(loc) {
            continue;
        }
        let sym = if !d.is_user_variable() {
            LocalIdent::anon(loc)
        } else {
            let x = body.var_debug_info.iter().find(|var_info| match var_info.value {
                Place(p) => p.as_local().map(|l| l == loc).unwrap_or(false),
                _ => false,
            });

            let debug_info = x.expect("expected user variable to have name");

            let cnt = names.entry(debug_info.name).or_insert(0);

            let sym = if *cnt == 0 {
                debug_info.name
            } else {
                Symbol::intern(&format!("{}{}", debug_info.name, cnt))
            };

            let sym = LocalIdent::dbg_raw(loc, sym);

            *cnt += 1;
            sym
        };

        let symbol = sym.symbol();
        let mut i = 0;
        let mut s = symbol;
        while vars.contains_key(&s) {
            s = Symbol::intern(&format!("{}_{i}", symbol.as_str()));
            i += 1;
        }
        locals.insert(loc, s);
        let is_arg = 0 < loc.index() && loc.index() <= body.arg_count;
        vars.insert(
            s,
            LocalDecl {
                span: d.source_info.span,
                ty: d.ty,
                temp: !d.is_user_variable(),
                arg: is_arg,
            },
        );
    }
    (vars, locals)
}

fn mk_goto<'tcx>(bb: BasicBlock) -> fmir::Terminator<'tcx> {
    fmir::Terminator::Goto(bb)
}

#[derive(Clone)]
pub(crate) struct ClosureContract<'tcx> {
    pub(crate) resolve: (PreSignature<'tcx>, Term<'tcx>),
    pub(crate) precond: (PreSignature<'tcx>, Term<'tcx>),
    pub(crate) postcond_once: Option<(PreSignature<'tcx>, Term<'tcx>)>,
    pub(crate) postcond_mut: Option<(PreSignature<'tcx>, Term<'tcx>)>,
    pub(crate) postcond: Option<(PreSignature<'tcx>, Term<'tcx>)>,
    pub(crate) unnest: Option<(PreSignature<'tcx>, Term<'tcx>)>,
}

impl<'tcx> TranslationCtx<'tcx> {
    pub(crate) fn build_closure_contract(&mut self, def_id: DefId) -> ClosureContract<'tcx> {
        let TyKind::Closure(_, subst) = self.type_of(def_id).instantiate_identity().kind() else {
            unreachable!()
        };

        let kind = subst.as_closure().kind();
        let mut pre_clos_sig = self.sig(def_id).clone();

        let contract = contract_of(self, def_id);
        let mut postcondition: Term<'_> = contract.ensures_conj(self.tcx);
        let mut precondition: Term<'_> = contract.requires_conj(self.tcx);

        let result_ty = pre_clos_sig.output;
        pre_clos_sig.output = self.types.bool;

        pre_clos_sig.contract = PreContract::default();

        let args: Vec<_> = pre_clos_sig.inputs.drain(1..).collect();

        if args.len() == 0 {
            pre_clos_sig.inputs.push((Symbol::intern("_"), DUMMY_SP, self.types.unit))
        } else {
            let arg_tys: Vec<_> = args.iter().map(|(_, _, ty)| *ty).collect();
            let arg_ty = Ty::new_tup(self.tcx, &arg_tys);

            pre_clos_sig.inputs.push((Symbol::intern("args"), DUMMY_SP, arg_ty));

            let arg_tuple = Term::var(Symbol::intern("args"), arg_ty);

            let arg_pat = pearlite::Pattern::Tuple(
                args.iter()
                    .enumerate()
                    .map(|(idx, (nm, _, _))| {
                        if nm.is_empty() {
                            // We skipped the first element
                            pearlite::Pattern::Binder(anonymous_param_symbol(idx + 1))
                        } else {
                            pearlite::Pattern::Binder(*nm)
                        }
                    })
                    .collect(),
            );

            postcondition = pearlite::Term {
                span: postcondition.span,
                kind: TermKind::Let {
                    pattern: arg_pat.clone(),
                    arg: Box::new(arg_tuple.clone()),
                    body: Box::new(postcondition),
                },
                ty: self.types.bool,
            };
            precondition = pearlite::Term {
                span: precondition.span,
                kind: TermKind::Let {
                    pattern: arg_pat,
                    arg: Box::new(arg_tuple),
                    body: Box::new(precondition),
                },
                ty: self.types.bool,
            };
        }

        let mut post_sig = pre_clos_sig.clone();
        let pre_sig = pre_clos_sig;

        post_sig.inputs.push((Symbol::intern("result"), DUMMY_SP, result_ty));

        let env_ty = self
            .closure_env_ty(
                self.type_of(def_id).instantiate_identity(),
                kind,
                self.lifetimes.re_erased,
            )
            .peel_refs();
        let self_ty = env_ty;

        let precond = {
            // Preconditions are the same for every kind of closure
            let mut pre_sig = pre_sig;

            pre_sig.inputs[0].0 = Symbol::intern("self");
            pre_sig.inputs[0].2 = self_ty;

            let mut subst =
                closure_capture_subst(self.tcx, def_id, subst, None, Symbol::intern("self"));

            let mut precondition = precondition.clone();
            subst.visit_mut_term(&mut precondition);

            (pre_sig, precondition)
        };

        let mut resolve = closure_resolve(self, def_id, subst);
        resolve.1 = normalize(self.tcx, self.param_env(def_id), resolve.1);
        let mut contracts = ClosureContract {
            resolve,
            precond,
            postcond: None,
            postcond_once: None,
            postcond_mut: None,
            unnest: None,
        };

        if kind.extends(Fn) {
            let mut post_sig = post_sig.clone();

            post_sig.inputs[0].0 = Symbol::intern("self");
            post_sig.inputs[0].2 = self_ty;
            let mut csubst =
                closure_capture_subst(self.tcx, def_id, subst, Some(Fn), Symbol::intern("self"));
            let mut postcondition = postcondition.clone();

            csubst.visit_mut_term(&mut postcondition);

            contracts.postcond = Some((post_sig, postcondition));
        }

        if kind.extends(FnMut) {
            let mut post_sig = post_sig.clone();
            // post_sig.name = Ident::build("postcondition_mut");

            post_sig.inputs[0].0 = Symbol::intern("self");
            post_sig.inputs[0].2 = Ty::new_mut_ref(self.tcx, self.lifetimes.re_erased, self_ty);

            let mut csubst =
                closure_capture_subst(self.tcx, def_id, subst, Some(FnMut), Symbol::intern("self"));

            let mut postcondition = postcondition.clone();
            csubst.visit_mut_term(&mut postcondition);

            let args = subst.as_closure().sig().inputs().skip_binder()[0];
            let unnest_subst = self.mk_args(&[GenericArg::from(args), GenericArg::from(env_ty)]);

            let unnest_id = get_fn_mut_unnest(self.tcx);

            let mut postcondition: Term<'tcx> = postcondition;
            postcondition = postcondition.conj(Term::call_no_normalize(
                self.tcx,
                unnest_id,
                unnest_subst,
                vec![
                    Term::var(
                        Symbol::intern("self"),
                        Ty::new_mut_ref(self.tcx, self.lifetimes.re_erased, self_ty),
                    )
                    .cur(),
                    Term::var(
                        Symbol::intern("self"),
                        Ty::new_mut_ref(self.tcx, self.lifetimes.re_erased, self_ty),
                    )
                    .fin(),
                ],
            ));

            postcondition = normalize(self.tcx, self.param_env(def_id), postcondition);

            let unnest_sig =
                EarlyBinder::bind(self.sig(unnest_id).clone()).instantiate(self.tcx, unnest_subst);

            let mut unnest = closure_unnest(self.tcx, def_id, subst);
            unnest = normalize(self.tcx, self.param_env(def_id), unnest);

            contracts.unnest = Some((unnest_sig, unnest));
            contracts.postcond_mut = Some((post_sig, postcondition));
        }

        if kind.extends(FnOnce) {
            let mut post_sig = post_sig.clone();
            post_sig.inputs[0].0 = Symbol::intern("self");
            post_sig.inputs[0].2 = self_ty;

            let mut csubst = closure_capture_subst(
                self.tcx,
                def_id,
                subst,
                Some(FnOnce),
                Symbol::intern("self"),
            );

            let mut postcondition = postcondition.clone();
            csubst.visit_mut_term(&mut postcondition);

            contracts.postcond_once = Some((post_sig, postcondition));
        }

        contracts
    }
}

fn closure_resolve<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> (PreSignature<'tcx>, Term<'tcx>) {
    let mut resolve = Term::mk_true(ctx.tcx);

    let self_ = Term::var(Symbol::intern("_1"), ctx.type_of(def_id).instantiate_identity());
    let csubst = subst.as_closure();
    let param_env = ctx.param_env(def_id);
    for (ix, ty) in csubst.upvar_tys().iter().enumerate() {
        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self_.clone()), name: ix.into() },
            span: DUMMY_SP,
        };

        if let Some((id, subst)) = resolve_predicate_of(ctx, param_env, ty) {
            resolve = Term::call(ctx.tcx, param_env, id, subst, vec![proj]).conj(resolve);
        }
    }

    let sig = PreSignature {
        inputs: vec![(
            Symbol::intern("_1"),
            ctx.def_span(def_id),
            ctx.type_of(def_id).instantiate_identity(),
        )],
        output: ctx.types.bool,
        contract: PreContract::default(),
    };

    (sig, resolve)
}

fn closure_unnest<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Term<'tcx> {
    let ty = Ty::new_closure(tcx, def_id, subst);
    let kind = subst.as_closure().kind();
    let env_ty = tcx.closure_env_ty(ty, kind, tcx.lifetimes.re_erased).peel_refs();

    let self_ = Term::var(Symbol::intern("self"), env_ty);

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
                    kind: TermKind::Projection { lhs: Box::new(lhs), name: ix.into() },
                    span: DUMMY_SP,
                };
                let cur = self_.clone();
                let fin = Term::var(Symbol::intern("_2"), env_ty);

                use rustc_middle::ty::BorrowKind;

                let unnest_one = match is_mut {
                    BorrowKind::ImmBorrow => Term::eq(tcx, (acc)(fin), (acc)(cur)),
                    _ => Term::eq(tcx, (acc)(fin).fin(), (acc)(cur).fin()),
                };

                unnest = unnest_one.conj(unnest);
            }
        }
    }

    unnest
}

// Responsible for replacing occurences of captured variables with projections from the closure environment.
// Must also account for the *kind* of capture and the *kind* of closure involved each time.
pub(crate) struct ClosureSubst<'tcx> {
    self_: Term<'tcx>,
    kind: Option<ClosureKind>,

    map: IndexMap<Symbol, (UpvarCapture, Ty<'tcx>, FieldIdx)>,
    bound: HashSet<Symbol>,
}

impl<'tcx> ClosureSubst<'tcx> {
    // TODO: Simplify this logic.
    fn var(&self, x: Symbol) -> Option<Term<'tcx>> {
        let (ck, ty, ix) = *self.map.get(&x)?;

        let self_ = match self.kind {
            None => self.self_.clone(),
            Some(ClosureKind::Fn) => self.self_.clone().cur(),
            Some(ClosureKind::FnMut) => self.self_.clone().fin(),
            Some(ClosureKind::FnOnce) => self.self_.clone(),
        };

        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self_), name: ix },
            span: DUMMY_SP,
        };

        match ck {
            UpvarCapture::ByValue => Some(proj),
            UpvarCapture::ByRef(BorrowKind::MutBorrow | BorrowKind::UniqueImmBorrow)
                if self.kind == Some(ClosureKind::FnOnce) =>
            {
                Some(proj.fin())
            }
            UpvarCapture::ByRef(_) => Some(proj.cur()),
        }
    }

    fn old(&self, x: Symbol) -> Option<Term<'tcx>> {
        let (ck, ty, ix) = *self.map.get(&x)?;

        let self_ = match self.kind {
            Some(ClosureKind::Fn) => self.self_.clone().cur(),
            Some(ClosureKind::FnMut) => self.self_.clone().cur(),
            Some(ClosureKind::FnOnce) => self.self_.clone(),
            None => unreachable!(),
        };

        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self_), name: ix },
            span: DUMMY_SP,
        };

        match ck {
            UpvarCapture::ByValue => Some(proj),
            UpvarCapture::ByRef(_) => Some(proj.cur()),
        }
    }
}

impl<'tcx> TermVisitorMut<'tcx> for ClosureSubst<'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        match &mut term.kind {
            TermKind::Old { term: box Term { kind: TermKind::Var(x), .. }, .. } => {
                if !self.bound.contains(&x) {
                    if let Some(v) = self.old(*x) {
                        *term = v;
                    }
                    return;
                }
            }
            TermKind::Var(x) => {
                if !self.bound.contains(&x) {
                    if let Some(v) = self.var(*x) {
                        *term = v;
                    }
                }
            }
            TermKind::Quant { binder, .. } => {
                let mut bound = self.bound.clone();
                for name in &binder.0 {
                    bound.insert(name.name);
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
                bound.extend(bound_new.iter());
                std::mem::swap(&mut self.bound, &mut bound);
                self.visit_mut_term(body);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            _ => super_visit_mut_term(term, self),
        }
    }
}

pub(crate) fn closure_capture_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    cs: GenericArgsRef<'tcx>,
    // What kind of substitution we should generate. The same precondition can be used in several ways
    ck: Option<ClosureKind>,
    self_name: Symbol,
) -> ClosureSubst<'tcx> {
    let mut fun_def_id = def_id;
    while tcx.is_closure_like(fun_def_id) {
        fun_def_id = tcx.parent(fun_def_id);
    }

    let captures = tcx.closure_captures(def_id.expect_local());

    let ty = match ck {
        Some(ClosureKind::Fn) => Ty::new_imm_ref(
            tcx,
            tcx.lifetimes.re_erased,
            tcx.type_of(def_id).instantiate_identity(),
        ),
        Some(ClosureKind::FnMut) => Ty::new_mut_ref(
            tcx,
            tcx.lifetimes.re_erased,
            tcx.type_of(def_id).instantiate_identity(),
        ),
        Some(ClosureKind::FnOnce) | None => tcx.type_of(def_id).instantiate_identity(),
    };

    let self_ = Term::var(self_name, ty);

    let subst = std::iter::zip(captures, cs.as_closure().upvar_tys())
        .enumerate()
        .map(|(ix, (cap, ty))| (cap.to_symbol(), (cap.info.capture_kind, ty, ix.into())))
        .collect();

    ClosureSubst { self_, kind: ck, map: subst, bound: Default::default() }
}

fn resolve_predicate_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let trait_meth_id = get_resolve_method(ctx.tcx);
    let substs = ctx.mk_args(&[GenericArg::from(ty)]);

    // Optimization: if we know there is no Resolve instance for this type, then we do not emit
    // a resolve
    if !ty.is_closure()
        && matches!(
            traits::TraitResolved::resolve_item(ctx.tcx, param_env, trait_meth_id, substs),
            traits::TraitResolved::NoInstance
        )
    {
        return None;
    }

    Some((get_resolve_function(ctx.tcx), substs))
}
