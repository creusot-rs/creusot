use super::{
    fmir::{LocalDecls, LocalIdent, RValue},
    pearlite::{normalize, Term},
    specification::inv_subst,
};
use crate::{
    ctx::*,
    fmir::{self, Expr},
    gather_spec_closures::{
        assertions_and_ghosts, corrected_invariant_names_and_locations, LoopSpecKind,
    },
    resolve::EagerResolver,
    translation::{
        fmir::LocalDecl,
        pearlite::{self, TermKind, TermVisitorMut},
        specification::{contract_of, PreContract},
        traits,
    },
    util::{self, PreSignature},
};
use indexmap::IndexMap;
use rustc_borrowck::borrow_set::BorrowSet;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;

use rustc_middle::{
    mir::{self, traversal::reverse_postorder, BasicBlock, Body, Local, Location, Operand, Place},
    ty::{
        subst::{GenericArg, SubstsRef},
        ClosureKind::*,
        EarlyBinder, ParamEnv, Ty, TyCtxt, TyKind, UpvarCapture,
    },
};
use rustc_span::{Symbol, DUMMY_SP};
use std::{collections::HashMap, iter, rc::Rc};
// use why3::declaration::*;

pub(crate) mod promoted;
mod statement;
pub(crate) mod terminator;

pub(crate) fn fmir<'tcx>(ctx: &mut TranslationCtx<'tcx>, body_id: BodyId) -> fmir::Body<'tcx> {
    let body = ctx.body(body_id).clone();

    // crate::debug::debug(ctx.tcx, ctx.tcx.optimized_mir(def_id));
    // crate::debug::debug(ctx.tcx, &body);

    let func_translator = BodyTranslator::build_context(ctx.tcx, ctx, &body, body_id);
    func_translator.translate()
}

// Split this into several sub-contexts: Core, Analysis, Results?
pub struct BodyTranslator<'body, 'tcx> {
    pub tcx: TyCtxt<'tcx>,

    body_id: BodyId,

    body: &'body Body<'tcx>,

    resolver: Option<EagerResolver<'body, 'tcx>>,

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

    borrows: Option<Rc<BorrowSet<'tcx>>>,

    // Translated locals
    locals: HashMap<Local, Symbol>,

    vars: LocalDecls<'tcx>,
}

impl<'body, 'tcx> BodyTranslator<'body, 'tcx> {
    fn build_context(
        tcx: TyCtxt<'tcx>,
        ctx: &'body mut TranslationCtx<'tcx>,
        body: &'body Body<'tcx>,
        body_id: BodyId,
    ) -> Self {
        let invariants = corrected_invariant_names_and_locations(ctx, &body);
        let assertions = assertions_and_ghosts(ctx, &body);
        let mut erased_locals = BitSet::new_empty(body.local_decls.len());

        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if crate::util::is_spec(tcx, *def_id) || util::is_ghost_closure(tcx, *def_id) {
                    erased_locals.insert(local);
                }
            }
        });

        let (resolver, borrows) = match body_id.promoted {
            None => {
                let with_facts = ctx.body_with_facts(body_id.def_id);
                let borrows = with_facts.borrow_set.clone();
                let resolver = EagerResolver::new(
                    tcx,
                    body,
                    borrows.clone(),
                    with_facts.region_inference_context.clone(),
                );

                // eprintln!("body of {}", tcx.def_path_str(body_id.def_id()));
                // resolver.debug(with_facts.regioncx.clone());

                (Some(resolver), Some(borrows))
            }
            Some(_) => (None, None),
        };

        let (vars, locals) = translate_vars(&body, &erased_locals);

        BodyTranslator {
            tcx,
            body,
            body_id,
            resolver,
            locals,
            vars,
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

        assert!(self.assertions.is_empty(), "unused assertions");
        assert!(self.invariants.is_empty(), "unused invariants");

        fmir::Body { locals: self.vars, arg_count, blocks: self.past_blocks }
    }

    fn translate_body(&mut self) {
        for (bb, bbd) in reverse_postorder(self.body) {
            self.current_block = (vec![], None);
            if bbd.is_cleanup {
                continue;
            }

            for (kind, mut body) in self.invariants.remove(&bb).unwrap_or_else(Vec::new) {
                body.subst(&inv_subst(
                    self.body,
                    &self.locals,
                    *self.body.source_info(bb.start_location()),
                ));
                self.check_ghost_term(&body, bb.start_location());
                match kind {
                    LoopSpecKind::Variant => self.emit_statement(fmir::Statement::Variant(body)),
                    LoopSpecKind::Invariant => {
                        self.emit_statement(fmir::Statement::Invariant(body))
                    }
                }
            }

            self.resolve_locals_between_blocks(bb);

            let mut loc = bb.start_location();

            for statement in &bbd.statements {
                self.translate_statement(statement, loc);
                loc = loc.successor_within_block();
            }

            self.translate_terminator(bbd.terminator(), loc);

            if let Some(resolver) = &mut self.resolver && bbd.terminator().successors().next().is_none() {
                let mut resolved = resolver.need_resolve_locals_before(loc);
                resolved.remove(Local::from_usize(0)); // do not resolve return local
                self.resolve_locals(resolved);
            }

            let block = fmir::Block {
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

    fn emit_resolve(&mut self, pl: Place<'tcx>) {
        let place_ty = pl.ty(self.body, self.ctx.tcx).ty;
        if let Some((id, subst)) = resolve_predicate_of(self.ctx, self.param_env(), place_ty) {
            let p = self.translate_place(pl);

            if let Some((_, s)) = self.ctx.type_invariant(self.body_id.def_id(), place_ty) {
                self.emit_statement(fmir::Statement::AssertTyInv(s.type_at(0), p.clone()));
            }

            self.emit_statement(fmir::Statement::Resolve(id, subst, p));
        }
    }

    fn emit_terminator(&mut self, t: fmir::Terminator<'tcx>) {
        assert!(self.current_block.1.is_none());

        self.current_block.1 = Some(t);
    }

    fn emit_borrow(&mut self, lhs: &Place<'tcx>, rhs: &Place<'tcx>) {
        let p = self.translate_place(*rhs);
        self.emit_assignment(lhs, fmir::RValue::Borrow(p));

        let rhs_ty = rhs.ty(self.body, self.ctx.tcx).ty;
        if let Some((_, s)) = self.ctx.type_invariant(self.body_id.def_id(), rhs_ty) {
            let p = self.translate_place(*lhs);
            self.emit_statement(fmir::Statement::AssumeTyInv(s.type_at(0), p));
        }
    }

    fn emit_ghost_assign(&mut self, lhs: Place<'tcx>, rhs: Term<'tcx>) {
        self.emit_assignment(&lhs, fmir::RValue::Ghost(rhs))
    }

    fn emit_assignment(&mut self, lhs: &Place<'tcx>, rhs: RValue<'tcx>) {
        let p = self.translate_place(*lhs);
        self.emit_statement(fmir::Statement::Assignment(p, rhs));
    }

    // Inserts resolves for locals which died over the course of a goto or switch
    fn resolve_locals_between_blocks(&mut self, bb: BasicBlock) {
        let Some(resolver) = &mut self.resolver else { return; };
        let pred_blocks = &self.body.basic_blocks.predecessors()[bb];

        if pred_blocks.is_empty() {
            return;
        }

        let resolved_between = pred_blocks
            .iter()
            .map(|pred| resolver.resolved_locals_between_blocks(*pred, bb))
            .collect::<Vec<_>>();

        // If we have multiple predecessors (join point) but all of them agree on the deaths, then don't introduce a dedicated block.
        if resolved_between.windows(2).all(|r| r[0] == r[1]) {
            self.resolve_locals(resolved_between.into_iter().next().unwrap());
            return;
        }

        for (pred, resolved) in iter::zip(pred_blocks, resolved_between) {
            // If no resolves occured in block transition then skip entirely
            if resolved.count() == 0 {
                continue;
            };

            // Otherwise, we emit the resolves and move them to a stand-alone block.
            self.resolve_locals(resolved);
            let resolve_block = fmir::Block {
                stmts: std::mem::take(&mut self.current_block.0),
                terminator: fmir::Terminator::Goto(bb),
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

    fn resolve_locals(&mut self, mut locals: BitSet<Local>) {
        locals.subtract(&self.erased_locals.to_hybrid());

        // TODO determine resolution order based on outlives relation
        let locals = locals.iter().collect::<Vec<_>>();
        for local in locals.into_iter().rev() {
            self.emit_resolve(local.into());
        }
    }

    // Useful helper to translate an operand
    pub(crate) fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Expr<'tcx> {
        match operand {
            Operand::Copy(pl) => Expr::Copy(self.translate_place(*pl)),
            Operand::Move(pl) => Expr::Move(self.translate_place(*pl)),
            Operand::Constant(c) => {
                crate::constant::from_mir_constant(self.param_env(), self.ctx, c)
            }
        }
    }

    fn translate_place(&self, _pl: mir::Place<'tcx>) -> fmir::Place<'tcx> {
        let projection = _pl
            .projection
            .into_iter()
            .map(|p| match p {
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
            })
            .collect();
        fmir::Place { local: self.locals[&_pl.local], projection }
    }

    fn check_ghost_term(&mut self, term: &Term<'tcx>, location: Location) {
        if let Some(resolver) = &mut self.resolver {
            let frozen = resolver.frozen_locals_before(location);
            let free_vars = term.free_vars();
            for f in frozen.iter() {
                if free_vars.contains(&self.locals[&f]) {
                    let msg = format!("Use of borrowed variable {}", self.locals[&f]);
                    self.ctx.crash_and_error(term.span, &msg);
                }
            }
        }
    }
}

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

        locals.insert(loc, sym.symbol());
        vars.insert(
            sym.symbol(),
            LocalDecl {
                mir_local: loc,
                span: d.source_info.span,
                ty: d.ty,
                temp: !d.is_user_variable(),
                arg: 0 < loc.index() && loc.index() <= body.arg_count,
            },
        );
    }
    (vars, locals)
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

        let unnest_sig = EarlyBinder::bind(ctx.sig(unnest_id).clone()).subst(ctx.tcx, unnest_subst);

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

    let self_ = Term::var(Symbol::intern("_1"), ctx.type_of(def_id).subst_identity());
    let csubst = subst.as_closure();
    let param_env = ctx.param_env(def_id);
    for (ix, ty) in csubst.upvar_tys().enumerate() {
        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self_.clone()), name: ix.into() },
            span: DUMMY_SP,
        };

        if let Some((id, subst)) = resolve_predicate_of(ctx, param_env, ty) {
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
            Symbol::intern("_1"),
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

pub(crate) fn resolve_predicate_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    let trait_meth_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve_method"))?;
    let subst = ctx.mk_substs(&[GenericArg::from(ty)]);

    let resolve_impl = traits::resolve_opt(ctx.tcx, param_env, trait_meth_id, subst)?;
    use rustc_middle::ty::TypeVisitableExt;
    if !ty.still_further_specializable()
        && ctx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), resolve_impl.0)
        && !resolve_impl.1.type_at(0).is_closure()
    {
        return None;
    }

    Some(resolve_impl)
}
