mod statement;
mod terminator;

use crate::{
    analysis::{self, BodyLocals, BodySpecs, BorrowData, ResolvedPlace},
    backend::{
        projections::projections_term,
        ty_inv::{inv_call, is_tyinv_trivial},
    },
    contracts_items::Intrinsic,
    ctx::*,
    translation::{
        constant::mirconst_to_operand,
        fmir::{self, LocalDecls, RValue, Variant},
        pearlite::{Ident, PIdent, Term, TermKind},
    },
};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::MixedBitSet;
use rustc_middle::{
    mir::{self, BasicBlock, Body, Local, Location, Operand, Place, traversal::reverse_postorder},
    ty::{Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::{DUMMY_SP, Span};
use std::{assert_matches::assert_matches, collections::HashMap, ops::FnOnce};

pub(crate) use self::terminator::discriminator_for_switch;

/// Translate a function from rustc's MIR to fMIR.
pub(crate) fn fmir<'tcx>(ctx: &TranslationCtx<'tcx>, body_id: BodyId) -> fmir::Body<'tcx> {
    BodyTranslator::with_context(ctx, body_id, |func_translator| func_translator.translate())
}

/// Translate a MIR body (rustc) to FMIR (creusot).
// TODO: Split this into several sub-contexts: Core, Analysis, Results?
struct BodyTranslator<'a, 'tcx> {
    body_id: BodyId,

    body: &'a Body<'tcx>,
    borrow_data: Option<BorrowData<'tcx>>,
    typing_env: TypingEnv<'tcx>,

    /// Current block being generated
    current_block: (Vec<fmir::Statement<'tcx>>, Option<fmir::Terminator<'tcx>>),

    past_blocks: IndexMap<BasicBlock, fmir::Block<'tcx>>,
    retarget_blocks: Vec<(BasicBlock, fmir::Block<'tcx>)>,

    // Type translation context
    ctx: &'a TranslationCtx<'tcx>,

    // Fresh BlockId
    fresh_id: usize,

    /// Store invariants.
    ///
    /// The basic block is the loop entry. It then contains a series of
    /// invariants, each with a possible description for Why3.
    invariants: HashMap<BasicBlock, Vec<(String, Term<'tcx>)>>,
    /// Maps a basic block representing a loop head to the variant of the loop.
    loop_variants: HashMap<BasicBlock, (Term<'tcx>, Ident)>,
    /// Names for the eventual variant for the function.
    ///
    /// This identifier is the name of the variable holding the variant's value
    /// at the start of the function
    function_variant: Ident,
    /// Invariants to translate as assertions.
    invariant_assertions: HashMap<DefId, (Term<'tcx>, String)>,
    /// Map of the `proof_assert!` blocks to their translated version.
    assertions: HashMap<DefId, Term<'tcx>>,
    /// Map of the `snapshot!` blocks to their translated version.
    snapshots: HashMap<DefId, Term<'tcx>>,

    // Translated locals
    locals: HashMap<Local, Ident>,

    // Variables that contain snapshots and specs.
    erased_locals: MixedBitSet<Local>,

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
        match self {
            TranslationError::PtrDeref => ctx.dcx().span_fatal(span, "Dereference of a raw pointer is forbidden in creusot: use `creusot_std::ghost::perm::Perm<*const T>` instead"),
        }
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
        let (body, body_specs, body_locals, borrow_data) = match body_id.def_id.as_local() {
            Some(def_id) => {
                let body_with_facts = ctx.body_with_facts(def_id);
                let body = match body_id.promoted {
                    None => &body_with_facts.body,
                    Some(promoted) => body_with_facts.promoted.get(promoted).unwrap(),
                };
                let mut body_specs = BodySpecs::from_body(ctx, body);
                let body_locals = BodyLocals::from_body(ctx, body, &body_specs.erased_locals);
                let borrow_data = match body_id.promoted {
                    None => Some(analysis::run_with_specs(
                        ctx,
                        body_with_facts,
                        &mut body_specs,
                        &body_locals,
                    )),
                    Some(_) => None,
                };
                (body, body_specs, body_locals, borrow_data)
            }
            None => {
                assert!(body_id.promoted.is_none());
                let body = ctx.tcx.mir_for_ctfe(body_id.def_id);
                let body_specs = BodySpecs::from_body(ctx, &body);
                let body_locals = BodyLocals::from_body(ctx, body, &body_specs.erased_locals);
                let borrow_data = None;
                (body, body_specs, body_locals, borrow_data)
            }
        };
        let typing_env = ctx.typing_env(body_id.def_id);
        let BodySpecs {
            invariants,
            variants,
            invariant_assertions,
            assertions,
            snapshots,
            erased_locals,
        } = body_specs;
        let BodyLocals { locals, vars } = body_locals;
        let mut loop_variants = HashMap::new();
        for (loop_head, term) in variants {
            let variant_old_name =
                Ident::fresh_local(format!("variant_old_bb{}", loop_head.as_usize()));
            loop_variants.insert(loop_head, (term, variant_old_name));
        }
        f(BodyTranslator {
            body,
            body_id,
            borrow_data,
            typing_env,
            locals,
            vars,
            erased_locals,
            current_block: (Vec::new(), None),
            past_blocks: Default::default(),
            retarget_blocks: vec![],
            ctx,
            fresh_id: body.basic_blocks.len(),
            invariants,
            loop_variants,
            function_variant: Ident::fresh_local("function_variant"),
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
            // compute invariants assertions to insert in this basic block
            for (expl, inv) in self.invariants.remove(&bb).into_iter().flatten() {
                invariants.push(fmir::Invariant { inv, expl });
            }

            // compute an eventual variant assertion to insert in this basic block
            if let Some((term, old_name)) = self.loop_variants.remove(&bb) {
                variant = Some(Variant { term, old_name: PIdent(old_name) });
            }

            let mut loc = bb.start_location();

            for statement in &bbd.statements {
                self.translate_statement(statement, loc);
                loc = loc.successor_within_block();
            }
            self.translate_terminator(bbd.terminator(), loc);

            let block = fmir::Block {
                invariants,
                variant,
                stmts: std::mem::take(&mut self.current_block.0),
                terminator: self.current_block.1.take().unwrap(),
            };

            self.past_blocks.insert(bb, block);
        }

        for (bb, block) in self.retarget_blocks {
            self.past_blocks.insert(bb, block);
        }

        assert!(self.assertions.is_empty(), "unused assertions");
        assert!(self.snapshots.is_empty(), "unused snapshots");
        assert!(self.invariants.is_empty(), "unused invariants");

        let variant_locals = self
            .past_blocks
            .values()
            .filter_map(|b| b.variant.as_ref().map(|v| (v.old_name, v.term.ty, v.term.span)))
            .collect();

        fmir::Body {
            locals: self.vars,
            variant_locals,
            function_variant: PIdent(self.function_variant),
            blocks: self.past_blocks,
            fresh: self.fresh_id,
            block_spans: self
                .body
                .basic_blocks
                .indices()
                .map(|bb| (bb, self.body.source_info(bb.start_location()).span))
                .collect(),
        }
    }

    fn resolve_at(&mut self, loc: Location, span: Span) {
        let Some(borrow_data) = &mut self.borrow_data else {
            return;
        };
        for place in borrow_data.remove_resolved_places_at(loc) {
            self.emit_resolve(place, span);
        }
    }

    fn typing_env(&self) -> TypingEnv<'tcx> {
        self.typing_env
    }

    fn emit_statement(&mut self, s: fmir::Statement<'tcx>) {
        self.current_block.0.push(s);
    }

    /// These types cannot contain mutable borrows and thus do not need to be resolved.
    fn skip_resolve_type(&self, ty: Ty<'tcx>) -> bool {
        let ty = self.ctx.normalize_erasing_regions(self.typing_env(), ty);
        self.tcx().type_is_copy_modulo_regions(self.typing_env(), ty)
        // The following is unsound because it does not take into account aliases.
        // It can be made technically sound, but anyway seems much less predictable than "we resolve
        // everything which is not Copy".
        // || !(ty.has_erased_regions() || ty.still_further_specializable())
    }

    fn emit_resolve_into(
        &self,
        rpl: ResolvedPlace<'tcx>,
        span: Span,
        dest: &mut Vec<fmir::Statement<'tcx>>,
    ) {
        let pl = match rpl {
            ResolvedPlace::All(pl) => pl,
            ResolvedPlace::PrivateFields(pl) => pl,
        };

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
            assert_matches!(rpl, ResolvedPlace::All(_));
            return;
        }

        let pl = self.translate_place(pl, span);
        if !is_tyinv_trivial(self.ctx, self.body_id.def_id, self.typing_env(), place_ty.ty, span) {
            let cond = projections_term(
                self.ctx,
                self.typing_env(),
                Term::var(pl.local, self.vars[&pl.local].ty),
                &pl.projection,
                |e| match rpl {
                    ResolvedPlace::All(_) => {
                        inv_call(self.ctx, self.typing_env(), self.body_id.def_id, e).unwrap()
                    }
                    ResolvedPlace::PrivateFields(_) => Term {
                        kind: TermKind::PrivateInv { term: Box::new(e) },
                        ty: self.ctx.types.bool,
                        span: DUMMY_SP,
                    },
                },
                Some(Term::true_(self.tcx())),
                |id| Term::var(*id, self.ctx.types.usize),
                span,
            );
            dest.push(fmir::Statement {
                kind: fmir::StatementKind::Assertion {
                    cond,
                    msg: Some("expl:type invariant".to_string()),
                    check: true,
                    assume: false,
                },
                span,
            })
        }

        let mut res_triv = true;

        let cond = projections_term(
            self.ctx,
            self.typing_env(),
            Term::var(pl.local, self.vars[&pl.local].ty),
            &pl.projection,
            |e| {
                let r = match rpl {
                    ResolvedPlace::All(_) => {
                        self.ctx.resolve(self.body_id.def_id, self.typing_env(), e)
                    }
                    ResolvedPlace::PrivateFields(_) => Term {
                        kind: TermKind::PrivateResolve { term: Box::new(e) },
                        ty: self.ctx.types.bool,
                        span: DUMMY_SP,
                    },
                };
                res_triv = res_triv && r.is_true();
                r
            },
            Some(Term::true_(self.tcx())),
            |id| Term::var(*id, self.ctx.types.usize),
            span,
        );
        if !res_triv {
            dest.push(fmir::Statement {
                kind: fmir::StatementKind::Assertion {
                    cond,
                    msg: None,
                    check: false,
                    assume: true,
                },
                span,
            })
        }
    }

    fn emit_resolve(&mut self, pl: ResolvedPlace<'tcx>, span: Span) {
        let mut dest = std::mem::take(&mut self.current_block.0);
        self.emit_resolve_into(pl, span, &mut dest);
        self.current_block.0 = dest;
    }

    fn emit_terminator(&mut self, t: fmir::Terminator<'tcx>) {
        assert!(self.current_block.1.is_none());

        self.current_block.1 = Some(t);
    }

    /// # Parameters
    ///
    /// `is_final` signals that the emitted borrow should be final: see [`NotFinalPlaces`].
    fn emit_mut_borrow(
        &mut self,
        lhs: Place<'tcx>,
        rhs: Place<'tcx>,
        is_final: fmir::BorrowKind,
        span: Span,
    ) {
        let rhs = self.translate_place(rhs, span);
        let lhs = self.translate_place(lhs, span);
        self.emit_statement(fmir::Statement {
            kind: fmir::StatementKind::MutBorrow(is_final, lhs, rhs),
            span,
        })
    }

    fn emit_snapshot_assign(&mut self, lhs: Place<'tcx>, rhs: Term<'tcx>, span: Span) {
        let subst = self.ctx.mk_args(&[rhs.ty.into()]);
        let ty =
            Ty::new_adt(self.tcx(), self.ctx.adt_def(Intrinsic::Snapshot.get(self.ctx)), subst);

        let rvalue = fmir::RValue::Operand(fmir::Operand::term(rhs.coerce(ty)));
        self.emit_assignment(lhs, rvalue, span)
    }

    fn emit_assignment(&mut self, lhs: Place<'tcx>, rhs: RValue<'tcx>, span: Span) {
        let p = self.translate_place(lhs, span);
        self.emit_statement(fmir::Statement { kind: fmir::StatementKind::Assignment(p, rhs), span })
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
    fn translate_operand(&self, operand: &Operand<'tcx>, span: Span) -> fmir::Operand<'tcx> {
        match operand {
            &Operand::Copy(pl) | &Operand::Move(pl) => {
                fmir::Operand::Place(self.translate_place(pl, span))
            }
            Operand::Constant(c) => {
                mirconst_to_operand(c, self.ctx, self.typing_env(), self.body_id.def_id)
            }
        }
    }

    /// Useful helper to translate a place
    ///
    /// # Errors
    ///
    /// Will error when trying to dereference a raw pointer.
    fn translate_place(&self, pl: Place<'tcx>, span: Span) -> fmir::Place<'tcx> {
        let projections = pl
            .iter_projections()
            .map(|(p, elem)| match elem {
                mir::ProjectionElem::Deref => {
                    if p.ty(self.body, self.tcx()).ty.is_raw_ptr() {
                        TranslationError::PtrDeref.crash(self.ctx, span);
                    }
                    mir::ProjectionElem::Deref
                }
                mir::ProjectionElem::Field(ix, ty) => mir::ProjectionElem::Field(ix, ty),
                mir::ProjectionElem::Index(l) => {
                    mir::ProjectionElem::Index(PIdent(self.locals[&l]))
                }
                mir::ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    mir::ProjectionElem::ConstantIndex { offset, min_length, from_end }
                }
                mir::ProjectionElem::Subslice { from, to, from_end } => {
                    mir::ProjectionElem::Subslice { from, to, from_end }
                }
                mir::ProjectionElem::Downcast(s, ix) => mir::ProjectionElem::Downcast(s, ix),
                mir::ProjectionElem::OpaqueCast(ty) => mir::ProjectionElem::OpaqueCast(ty),
                mir::ProjectionElem::UnwrapUnsafeBinder(ty) => {
                    mir::ProjectionElem::UnwrapUnsafeBinder(ty)
                }
            })
            .collect::<Box<[_]>>();
        fmir::Place { local: self.locals[&pl.local], projection: projections }
    }
}

impl<'body, 'tcx> HasTyCtxt<'tcx> for BodyTranslator<'body, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }
}
