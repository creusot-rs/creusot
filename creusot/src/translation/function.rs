mod statement;
mod terminator;

use crate::{
    analysis::resolve::{self, BodyData, BodySpecs},
    backend::ty_inv::is_tyinv_trivial,
    ctx::*,
    gather_spec_closures::LoopSpecKind,
    translation::{
        constant::from_mir_constant,
        fmir::{self, LocalDecls, RValue, TrivialInv, inline_pearlite_subst},
        pearlite::{Ident, Term},
    },
};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::MixedBitSet;
use rustc_middle::{
    mir::{
        self, BasicBlock, Body, Local, Location, Operand, Place, PlaceRef,
        traversal::reverse_postorder,
    },
    ty::{Ty, TyCtxt, TyKind, TypeVisitableExt, TypingEnv},
};
use rustc_span::Span;
use std::{collections::HashMap, ops::FnOnce};

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
    body_data: BodyData<'tcx>,
    typing_env: TypingEnv<'tcx>,

    /// Spec / Snapshot variables
    erased_locals: MixedBitSet<Local>,

    /// Current block being generated
    current_block: (Vec<fmir::Statement<'tcx>>, Option<fmir::Terminator<'tcx>>),

    past_blocks: IndexMap<BasicBlock, fmir::Block<'tcx>>,

    retarget_blocks: Vec<(BasicBlock, BasicBlock, BasicBlock)>,

    // Type translation context
    ctx: &'a TranslationCtx<'tcx>,

    // Fresh BlockId
    fresh_id: usize,

    invariants: HashMap<BasicBlock, Vec<(LoopSpecKind, Term<'tcx>)>>,
    /// Invariants to translate as assertions.
    invariant_assertions: HashMap<DefId, (Term<'tcx>, String)>,
    /// Map of the `proof_assert!` blocks to their translated version.
    assertions: HashMap<DefId, Term<'tcx>>,
    /// Map of the `snapshot!` blocks to their translated version.
    snapshots: HashMap<DefId, Term<'tcx>>,

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
        let body = match body_id.promoted {
            None => &body_with_facts.body,
            Some(promoted) => body_with_facts.promoted.get(promoted).unwrap(),
        };
        let typing_env = ctx.typing_env(body.source.def_id());
        let assertions = resolve::get_assertions(ctx, body);
        let body_data = resolve::resolve_analysis_for(tcx, &body_with_facts, &assertions);
        let BodySpecs {
            invariants,
            invariant_assertions,
            assertions,
            snapshots,
            locals,
            vars,
            erased_locals,
        } = assertions;
        f(BodyTranslator {
            body,
            body_id,
            body_data,
            typing_env,
            tree: &fmir::ScopeTree::build(body, ctx.tcx, &locals),
            locals,
            vars,
            erased_locals,
            current_block: (Vec::new(), None),
            past_blocks: Default::default(),
            retarget_blocks: vec![],
            ctx,
            fresh_id: body.basic_blocks.len(),
            invariants,
            invariant_assertions,
            assertions,
            snapshots,
        })
    }

    fn translate(mut self) -> fmir::Body<'tcx> {
        for (bb, bbd) in reverse_postorder(self.body) {
            self.current_block = (vec![], None);
            if bbd.is_cleanup {
                continue;
            }

            let mut invariants = Vec::new();
            let mut variant = None;

            let info = *self.body.source_info(bb.start_location());
            let places = self.tree.visible_places(info.scope);
            for (kind, mut body) in self.invariants.remove(&bb).unwrap_or_else(Vec::new) {
                body.subst(inline_pearlite_subst(self.ctx, &places));
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

            let mut loc = bb.start_location();

            for statement in &bbd.statements {
                self.resolve_at(loc);
                if let Err(err) = self.translate_statement(statement, loc) {
                    err.crash(self.ctx, statement.source_info.span);
                }
                loc = loc.successor_within_block();
            }
            self.resolve_at(loc);
            self.translate_terminator(bbd.terminator(), loc);

            let block = fmir::Block {
                invariants,
                variant,
                stmts: std::mem::take(&mut self.current_block.0),
                terminator: self.current_block.1.take().unwrap(),
            };

            self.past_blocks.insert(bb, block);
        }

        // TODO
        for (pred, bb, resolve_block_id) in self.retarget_blocks {
            self.past_blocks.get_mut(&pred).unwrap().terminator.retarget(bb, resolve_block_id);
        }

        assert!(self.assertions.is_empty(), "unused assertions");
        assert!(self.snapshots.is_empty(), "unused snapshots");
        assert!(self.invariants.is_empty(), "unused invariants");

        fmir::Body {
            locals: self.vars,
            arg_count: self.body.arg_count,
            blocks: self.past_blocks,
            fresh: self.fresh_id,
        }
    }

    fn resolve_at(&mut self, loc: Location) {
        todo!()
    }

    fn typing_env(&self) -> TypingEnv<'tcx> {
        self.typing_env.clone()
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

        let span = self.tcx().def_span(self.body_id.def_id()); // TODO: not a great span
        if !is_tyinv_trivial(self.tcx(), self.typing_env(), place_ty.ty, span) {
            self.emit_statement(fmir::Statement {
                kind: fmir::StatementKind::AssertTyInv { pl: p.clone() },
                span,
            });
        }

        if let Some((did, subst)) = self.ctx.resolve(self.typing_env(), place_ty.ty) {
            self.emit_statement(fmir::Statement {
                kind: fmir::StatementKind::Resolve { did, subst, pl: p },
                span,
            });
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
        let triv_inv = if is_tyinv_trivial(
            self.tcx(),
            self.typing_env(),
            rhs_ty,
            self.tcx().def_span(self.body_id.def_id()),
        ) {
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
        self.emit_statement(fmir::Statement { kind: fmir::StatementKind::Assignment(p, rhs), span })
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

    fn fresh_block_id(&mut self) -> BasicBlock {
        let id = BasicBlock::from_usize(self.fresh_id);
        self.fresh_id += 1;
        id
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
}

impl<'body, 'tcx> HasTyCtxt<'tcx> for BodyTranslator<'body, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}
