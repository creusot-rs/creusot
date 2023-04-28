use super::{
    fmir::{resolve_predicate_of2, RValue},
    pearlite::{normalize, Term},
};
use crate::{
    backend::place::translate_local,
    ctx::*,
    fmir::{self, Expr},
    gather_spec_closures::{corrected_invariant_names_and_locations, LoopSpecKind},
    resolve::EagerResolver,
    rustc_extensions::renumber,
    translation::{
        pearlite::{self, TermKind, TermVisitorMut},
        specification::{contract_of, PreContract},
    },
    util::{self, ident_of, PreSignature},
};
use indexmap::IndexMap;
use rustc_borrowck::borrow_set::BorrowSet;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::{
    mir::{
        traversal::reverse_postorder, BasicBlock, Body, Local, Location, MirPass, Operand, Place,
        VarDebugInfo,
    },
    ty::{
        subst::{GenericArg, SubstsRef},
        ClosureKind::*,
        EarlyBinder, GenericParamDef, GenericParamDefKind, ParamEnv, Ty, TyCtxt, TyKind,
        UpvarCapture, WithOptConstParam,
    },
};
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_transform::{cleanup_post_borrowck::CleanupPostBorrowck, simplify::*};
use rustc_span::{Span, Symbol, DUMMY_SP};
use std::rc::Rc;
use why3::declaration::*;

pub(crate) mod promoted;
mod statement;
pub(crate) mod terminator;

pub(crate) fn fmir<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> fmir::Body<'tcx> {
    // We use `mir_promoted` as it is the MIR required by borrowck which we will have run by this point
    let (body, _) = ctx.mir_promoted(WithOptConstParam::unknown(def_id.expect_local()));
    let mut body = body.borrow().clone();

    // crate::debug::debug(ctx.tcx, ctx.tcx.optimized_mir(def_id));
    // crate::debug::debug(ctx.tcx, &body);
    // Basic clean up, replace FalseEdges with Gotos. Could potentially also replace other statement with Nops.
    // Investigate if existing MIR passes do this as part of 'post borrowck cleanup'.
    CleanupPostBorrowck.run_pass(ctx.tcx, &mut body);
    SimplifyCfg::new("verify").run_pass(ctx.tcx, &mut body);

    let func_translator = BodyTranslator::build_context(ctx.tcx, ctx, &body, def_id);
    func_translator.translate()
}

// Split this into several sub-contexts: Core, Analysis, Results?
pub struct BodyTranslator<'body, 'tcx> {
    pub tcx: TyCtxt<'tcx>,

    def_id: DefId,

    body: &'body Body<'tcx>,

    resolver: EagerResolver<'body, 'tcx>,

    // Spec / Ghost variables
    erased_locals: BitSet<Local>,

    // Current block being generated
    current_block: (Vec<fmir::Statement<'tcx>>, Option<fmir::Terminator<'tcx>>),

    past_blocks: IndexMap<BasicBlock, fmir::Block<'tcx>>,

    // Type translation context
    ctx: &'body mut TranslationCtx<'tcx>,

    // Fresh BlockId
    fresh_id: usize,

    invariants: IndexMap<BasicBlock, Vec<(LoopSpecKind, Term<'tcx>)>>,

    assertions: IndexMap<DefId, Term<'tcx>>,

    borrows: Rc<BorrowSet<'tcx>>,
}

impl<'body, 'tcx> BodyTranslator<'body, 'tcx> {
    fn build_context(
        tcx: TyCtxt<'tcx>,
        ctx: &'body mut TranslationCtx<'tcx>,
        body: &'body Body<'tcx>,
        // names: &'body mut CloneMap<'tcx>,
        def_id: DefId,
    ) -> Self {
        let (invariants, assertions) = corrected_invariant_names_and_locations(ctx, def_id, &body);
        let mut erased_locals = BitSet::new_empty(body.local_decls.len());

        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if crate::util::is_spec(tcx, *def_id) {
                    erased_locals.insert(local);
                }
            }
        });

        let mut clean_body = body.clone();

        let infcx = tcx.infer_ctxt().build();
        renumber::renumber_mir(&infcx, &mut clean_body, &mut Default::default());

        let (_, move_paths) = MoveData::gather_moves(&clean_body, tcx, tcx.param_env(def_id))
            .unwrap_or_else(|_| ctx.crash_and_error(ctx.def_span(def_id), "illegal move"));
        let borrows = BorrowSet::build(tcx, &clean_body, true, &move_paths);
        let borrows = Rc::new(borrows);
        let resolver = EagerResolver::new(tcx, body);

        // crate::debug::debug(tcx, body);
        BodyTranslator {
            tcx,
            body,
            def_id,
            resolver,
            erased_locals,
            current_block: (Vec::new(), None),
            past_blocks: Default::default(),
            ctx,
            fresh_id: body.basic_blocks.len(),
            invariants,
            assertions,
            borrows,
        }
    }

    fn translate(mut self) -> fmir::Body<'tcx> {
        self.translate_body();

        let arg_count = self.body.arg_count;
        let vars = self.translate_vars();

        assert!(self.assertions.is_empty(), "unused assertions");
        assert!(self.invariants.is_empty(), "unused invariants");

        fmir::Body { locals: vars, arg_count, blocks: self.past_blocks }
    }

    fn translate_body(&mut self) {
        for (bb, bbd) in reverse_postorder(self.body) {
            self.current_block = (vec![], None);
            if bbd.is_cleanup {
                continue;
            }

            for (kind, body) in self.invariants.remove(&bb).unwrap_or_else(Vec::new) {
                match kind {
                    LoopSpecKind::Variant => self.emit_statement(fmir::Statement::Variant(body)),
                    LoopSpecKind::Invariant => {
                        self.emit_statement(fmir::Statement::Invariant(body))
                    }
                }
            }

            self.freeze_locals_between_blocks(bb);

            let mut loc = bb.start_location();

            for statement in &bbd.statements {
                self.translate_statement(statement, loc);
                self.freeze_borrows_dying_at(loc);
                loc = loc.successor_within_block();
            }

            self.translate_terminator(bbd.terminator(), loc);

            let block = fmir::Block {
                stmts: std::mem::take(&mut self.current_block.0),
                terminator: std::mem::replace(&mut self.current_block.1, None).unwrap(),
            };

            self.past_blocks.insert(bb, block);
        }
    }

    fn translate_vars(&mut self) -> Vec<(LocalIdent, Span, Ty<'tcx>)> {
        let mut vars = Vec::with_capacity(self.body.local_decls.len());

        for (loc, decl) in self.body.local_decls.iter_enumerated() {
            if self.erased_locals.contains(loc) {
                continue;
            }
            let ident = self.translate_local(loc);

            vars.push((ident, decl.source_info.span, decl.ty))
        }

        vars
    }

    fn param_env(&self) -> ParamEnv<'tcx> {
        self.ctx.param_env(self.def_id)
    }

    fn emit_statement(&mut self, s: fmir::Statement<'tcx>) {
        self.current_block.0.push(s);
    }

    fn emit_resolve(&mut self, pl: Place<'tcx>) {
        if let Some((id, subst)) =
            resolve_predicate_of2(self.ctx, self.param_env(), pl.ty(self.body, self.ctx.tcx).ty)
        {
            // self.emit_statement(fmir::Statement::Assume(
            //     Term { kind: TermKind::Call { id: id, subst: subst, fun: (), args: () }}
            // ));
            self.emit_statement(fmir::Statement::Resolve(id, subst, pl));
        }
    }

    fn emit_terminator(&mut self, t: fmir::Terminator<'tcx>) {
        assert!(self.current_block.1.is_none());

        self.current_block.1 = Some(t);
    }

    fn emit_borrow(&mut self, lhs: &Place<'tcx>, rhs: &Place<'tcx>) {
        self.emit_assignment(lhs, fmir::RValue::Borrow(*rhs));
    }

    fn emit_ghost_assign(&mut self, lhs: Place<'tcx>, rhs: Term<'tcx>) {
        self.emit_assignment(&lhs, fmir::RValue::Ghost(rhs))
    }

    fn emit_assignment(&mut self, lhs: &Place<'tcx>, rhs: RValue<'tcx>) {
        self.emit_statement(fmir::Statement::Assignment(*lhs, rhs));
    }

    // Inserts drop statements for variables which died over the course of a goto or switch
    fn freeze_locals_between_blocks(&mut self, bb: BasicBlock) {
        let pred_blocks = &self.body.basic_blocks.predecessors()[bb];

        if pred_blocks.is_empty() {
            return;
        }

        let dying_in_first = self.resolver.locals_resolved_between_blocks(pred_blocks[0], bb);
        let mut same_deaths = true;
        // If we have multiple predecessors (join point) but all of them agree on the deaths, then don't introduce a dedicated block.
        for pred in pred_blocks {
            let dying = self.resolver.locals_resolved_between_blocks(*pred, bb);
            same_deaths = same_deaths && dying_in_first == dying
        }

        if same_deaths {
            let dying = self.resolver.locals_resolved_between_blocks(pred_blocks[0], bb);
            self.freeze_locals(dying);
            return;
        }

        for pred in pred_blocks {
            let dying = self.resolver.locals_resolved_between_blocks(*pred, bb);

            // If no deaths occured in block transition then skip entirely
            if dying.count() == 0 {
                continue;
            };

            self.freeze_locals(dying);
            let deaths = std::mem::take(&mut self.current_block.0);
            // let deaths = deaths
            //     .into_iter()
            //     .flat_map(|d| d.to_why(self.ctx, self.names, self.body, self.param_env()))
            //     .collect();

            let drop_block = self.fresh_block_id();
            let pred_id = pred;

            // Otherwise, we emit the deaths and move them to a stand-alone block.
            self.past_blocks.get_mut(pred_id).unwrap().terminator.retarget(bb, drop_block);
            self.past_blocks.insert(
                drop_block,
                fmir::Block { stmts: deaths, terminator: fmir::Terminator::Goto(bb) },
            );
        }
    }

    fn fresh_block_id(&mut self) -> BasicBlock {
        let id = BasicBlock::from_usize(self.fresh_id);
        self.fresh_id += 1;
        id
    }

    fn freeze_borrows_dying_at(&mut self, loc: Location) {
        let dying = self.resolver.locals_resolved_at_loc(loc);
        self.freeze_locals(dying);
    }

    fn freeze_locals(&mut self, mut dying: BitSet<Local>) {
        dying.subtract(&self.erased_locals.to_hybrid());

        for local in dying.iter() {
            self.emit_resolve(local.into());
        }
    }

    // Useful helper to translate an operand
    pub(crate) fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Expr<'tcx> {
        match operand {
            Operand::Copy(pl) | Operand::Move(pl) => Expr::Place(*pl),
            Operand::Constant(c) => {
                crate::constant::from_mir_constant(self.param_env(), self.ctx, c)
            }
        }
    }

    fn translate_local(&self, loc: Local) -> LocalIdent {
        translate_local(&self.body, loc)
    }
}

/// A MIR local along with an optional human-readable name
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LocalIdent(Local, Option<Symbol>);

impl LocalIdent {
    pub(crate) fn anon(loc: Local) -> Self {
        LocalIdent(loc, None)
    }

    pub(crate) fn dbg_raw(loc: Local, name: Symbol) -> Self {
        LocalIdent(loc, Some(name))
    }

    pub(crate) fn dbg(loc: Local, dbg: &VarDebugInfo) -> Self {
        LocalIdent(loc, Some(dbg.name))
    }

    pub(crate) fn symbol(&self) -> Symbol {
        match &self.1 {
            Some(id) => Symbol::intern(&format!("{}_{}", &*ident_of(*id), self.0.index())),
            None => Symbol::intern(&format!("_{}", self.0.index())),
        }
    }

    pub(crate) fn ident(&self) -> why3::Ident {
        match &self.1 {
            Some(id) => format!("{}_{}", &*ident_of(*id), self.0.index()).into(),
            None => format!("_{}", self.0.index()).into(),
        }
    }
}

pub(crate) struct ClosureContract<'tcx> {
    pub(crate) resolve: (PreSignature<'tcx>, Term<'tcx>),
    pub(crate) precond: (PreSignature<'tcx>, Term<'tcx>),
    pub(crate) postcond_once: Option<(PreSignature<'tcx>, Term<'tcx>)>,
    pub(crate) postcond_mut: Option<(PreSignature<'tcx>, Term<'tcx>)>,
    pub(crate) postcond: Option<(PreSignature<'tcx>, Term<'tcx>)>,
    pub(crate) unnest: Option<(PreSignature<'tcx>, Term<'tcx>)>,
}

pub(crate) fn closure_contract<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> ClosureContract<'tcx> {
    let TyKind::Closure(_, subst) =  ctx.tcx.type_of(def_id).subst_identity().kind() else { unreachable!() };

    let kind = subst.as_closure().kind();
    let mut pre_clos_sig = ctx.sig(def_id).clone();

    let contract = contract_of(ctx, def_id);
    let mut postcondition: Term<'_> = contract.ensures_conj(ctx.tcx);
    let mut precondition: Term<'_> = contract.requires_conj(ctx.tcx);

    let result_ty = pre_clos_sig.output;
    pre_clos_sig.output = ctx.types.bool;

    pre_clos_sig.contract = PreContract::default();

    let args: Vec<_> = pre_clos_sig.inputs.drain(1..).collect();

    if args.len() == 0 {
        pre_clos_sig.inputs.push((Symbol::intern("_"), DUMMY_SP, ctx.tcx.mk_unit()))
    } else {
        let arg_tys: Vec<_> = args.iter().map(|(_, _, ty)| *ty).collect();
        let arg_ty = ctx.tcx.mk_tup(&arg_tys);

        pre_clos_sig.inputs.push((Symbol::intern("args"), DUMMY_SP, arg_ty));

        let arg_tuple = Term::var(Symbol::intern("args"), arg_ty);

        let arg_pat = pearlite::Pattern::Tuple(
            args.iter()
                .enumerate()
                .map(|(idx, (nm, _, _))| {
                    if nm.is_empty() {
                        // We skipped the first element
                        pearlite::Pattern::Binder(util::anonymous_param_symbol(idx + 1))
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
            ty: ctx.types.bool,
        };
        precondition = pearlite::Term {
            span: precondition.span,
            kind: TermKind::Let {
                pattern: arg_pat,
                arg: Box::new(arg_tuple),
                body: Box::new(precondition),
            },
            ty: ctx.types.bool,
        };
    }

    let mut post_sig = pre_clos_sig.clone();
    let pre_sig = pre_clos_sig;

    post_sig.inputs.push((Symbol::intern("result"), DUMMY_SP, result_ty));

    let env_ty = ctx.closure_env_ty(def_id, subst, ctx.lifetimes.re_erased).unwrap().peel_refs();
    let self_ty = env_ty;

    let precond = {
        // Preconditions are the same for every kind of closure
        let mut pre_sig = pre_sig;

        pre_sig.inputs[0].0 = Symbol::intern("self");
        pre_sig.inputs[0].2 = self_ty;

        let mut subst =
            util::closure_capture_subst(ctx.tcx, def_id, subst, None, Symbol::intern("self"));

        let mut precondition = precondition.clone();
        subst.visit_mut_term(&mut precondition);

        (pre_sig, precondition)
    };

    let mut resolve = closure_resolve(ctx, def_id, subst);
    normalize(ctx.tcx, ctx.param_env(def_id), &mut resolve.1);
    let mut contracts = ClosureContract {
        resolve,
        precond,
        postcond: None,
        postcond_once: None,
        postcond_mut: None,
        unnest: None,
    };

    if kind <= Fn {
        let mut post_sig = post_sig.clone();

        post_sig.inputs[0].0 = Symbol::intern("self");
        post_sig.inputs[0].2 = self_ty;
        let mut csubst =
            util::closure_capture_subst(ctx.tcx, def_id, subst, Some(Fn), Symbol::intern("self"));
        let mut postcondition = postcondition.clone();

        csubst.visit_mut_term(&mut postcondition);

        contracts.postcond = Some((post_sig, postcondition));
    }

    if kind <= FnMut {
        let mut post_sig = post_sig.clone();
        // post_sig.name = Ident::build("postcondition_mut");

        post_sig.inputs[0].0 = Symbol::intern("self");
        post_sig.inputs[0].2 = ctx.mk_mut_ref(ctx.lifetimes.re_erased, self_ty);

        let mut csubst = util::closure_capture_subst(
            ctx.tcx,
            def_id,
            subst,
            Some(FnMut),
            Symbol::intern("self"),
        );

        let mut postcondition = postcondition.clone();
        csubst.visit_mut_term(&mut postcondition);

        let args = subst.as_closure().sig().inputs().skip_binder()[0];
        let unnest_subst = ctx.mk_substs(&[GenericArg::from(args), GenericArg::from(env_ty)]);

        let unnest_id = ctx.get_diagnostic_item(Symbol::intern("fn_mut_impl_unnest")).unwrap();

        let mut postcondition: Term<'tcx> = postcondition;
        postcondition = postcondition.conj(Term {
            ty: ctx.types.bool,
            kind: TermKind::Call {
                id: unnest_id.into(),
                subst: unnest_subst,
                fun: Box::new(Term::item(ctx.tcx, unnest_id, unnest_subst)),
                args: vec![
                    Term::var(
                        Symbol::intern("self"),
                        ctx.mk_mut_ref(ctx.lifetimes.re_erased, self_ty),
                    )
                    .cur(),
                    Term::var(
                        Symbol::intern("self"),
                        ctx.mk_mut_ref(ctx.lifetimes.re_erased, self_ty),
                    )
                    .fin(),
                ],
            },
            span: DUMMY_SP,
        });

        normalize(ctx.tcx, ctx.param_env(def_id), &mut postcondition);

        let unnest_sig = EarlyBinder(ctx.sig(unnest_id).clone()).subst(ctx.tcx, unnest_subst);

        let mut unnest = closure_unnest(ctx.tcx, def_id, subst);
        normalize(ctx.tcx, ctx.param_env(def_id), &mut unnest);

        contracts.unnest = Some((unnest_sig, unnest));
        contracts.postcond_mut = Some((post_sig, postcondition));
    }

    if kind <= FnOnce {
        let mut post_sig = post_sig.clone();
        post_sig.inputs[0].0 = Symbol::intern("self");
        post_sig.inputs[0].2 = self_ty;

        let mut csubst = util::closure_capture_subst(
            ctx.tcx,
            def_id,
            subst,
            Some(FnOnce),
            Symbol::intern("self"),
        );

        let mut postcondition = postcondition.clone();
        csubst.visit_mut_term(&mut postcondition);

        contracts.postcond_once = Some((post_sig, postcondition));
    }

    return contracts;
}

fn closure_resolve<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> (PreSignature<'tcx>, Term<'tcx>) {
    let mut resolve = Term::mk_true(ctx.tcx);

    let self_ = Term::var(Symbol::intern("_1'"), ctx.type_of(def_id).subst_identity());
    let csubst = subst.as_closure();
    let param_env = ctx.param_env(def_id);
    for (ix, ty) in csubst.upvar_tys().enumerate() {
        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self_.clone()), name: ix.into() },
            span: DUMMY_SP,
        };

        if let Some((id, subst)) = resolve_predicate_of2(ctx, param_env, ty) {
            resolve = Term {
                ty: ctx.types.bool,
                kind: TermKind::Call {
                    id: id.into(),
                    subst,
                    fun: Box::new(Term::item(ctx.tcx, id, subst)),
                    args: vec![proj],
                },
                span: DUMMY_SP,
            }
            .conj(resolve);
        }
    }

    let sig = PreSignature {
        inputs: vec![(
            Symbol::intern("_1'"),
            ctx.def_span(def_id),
            ctx.type_of(def_id).subst_identity(),
        )],
        output: ctx.types.bool,
        contract: PreContract::default(),
    };

    (sig, resolve)
}

pub(crate) fn closure_unnest<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Term<'tcx> {
    let env_ty = tcx.closure_env_ty(def_id, subst, tcx.lifetimes.re_erased).unwrap().peel_refs();

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
                let fin = Term::var(Symbol::intern("_2'"), env_ty);

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

// Closures inherit the generic parameters of the original function they were defined in, but
// add 3 'ghost' generics tracking metadata about the closure. We choose to erase those parameters,
// as they contain a function type along with other irrelevant details (for us).
pub(crate) fn closure_generic_decls(
    tcx: TyCtxt,
    mut def_id: DefId,
) -> impl Iterator<Item = Decl> + '_ {
    loop {
        if tcx.is_closure(def_id) {
            def_id = tcx.parent(def_id);
        } else {
            break;
        }
    }

    all_generic_decls_for(tcx, def_id)
}

pub(crate) fn all_generic_decls_for(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = Decl> + '_ {
    let generics = tcx.generics_of(def_id);

    generic_decls((0..generics.count()).map(move |i| generics.param_at(i, tcx)))
}

pub(crate) fn own_generic_decls_for(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = Decl> + '_ {
    let generics = tcx.generics_of(def_id);
    generic_decls(generics.params.iter())
}

fn generic_decls<'tcx, I: Iterator<Item = &'tcx GenericParamDef> + 'tcx>(
    it: I,
) -> impl Iterator<Item = Decl> + 'tcx {
    it.filter_map(|param| {
        if let GenericParamDefKind::Type { .. } = param.kind {
            Some(Decl::TyDecl(TyDecl::Opaque {
                ty_name: (&*param.name.as_str().to_lowercase()).into(),
                ty_params: vec![],
            }))
        } else {
            None
        }
    })
}
