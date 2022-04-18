use crate::{
    gather_spec_closures::GatherSpecClosures,
    rustc_extensions::renumber,
    translation::{
        specification::contract_of,
        ty::{closure_accessors, translate_closure_ty, translate_ty},
    },
    util::{self, ident_of, signature_of},
};
use rustc_borrowck::borrow_set::BorrowSet;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::subst::{GenericArg, SubstsRef};
use rustc_middle::ty::Ty;
use rustc_middle::ty::{GenericParamDef, GenericParamDefKind};
use rustc_middle::{
    mir::traversal::preorder,
    mir::{BasicBlock, Body, Local, Location, MirPass, Operand, VarDebugInfo},
    ty::TyCtxt,
    ty::{TyKind, WithOptConstParam},
};
use rustc_middle::{mir::Place, ty::DefIdTree};
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_mir_transform::{remove_false_edges::*, simplify::*};
use rustc_span::{Symbol, DUMMY_SP};
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;
use why3::mlcfg::{self, Statement::*, *};
use why3::{declaration::*, Ident};

use indexmap::IndexMap;

mod place;
mod statement;
mod terminator;

use crate::ctx::*;
use crate::translation::{traits, ty};

pub fn translate_function<'tcx, 'sess>(
    ctx: &mut TranslationCtx<'sess, 'tcx>,
    def_id: DefId,
) -> Module {
    let tcx = ctx.tcx;
    let mut names = CloneMap::new(tcx, def_id, true);
    names.clone_self(def_id);

    assert!(def_id.is_local(), "translate_function: expected local DefId");

    if util::is_trusted(tcx, def_id) || !util::has_body(ctx, def_id) {
        if util::has_body(ctx, def_id) {
            tcx.ensure().mir_borrowck(def_id.expect_local());
        }
        return translate_trusted(tcx, ctx, def_id);
    }

    let gather = GatherSpecClosures::gather(ctx, &mut names, def_id);
    tcx.ensure().mir_borrowck(def_id.expect_local());
    let (body, _) = tcx.mir_promoted(WithOptConstParam::unknown(def_id.expect_local()));
    let mut body = body.borrow().clone();
    // Basic clean up, replace FalseEdges with Gotos. Could potentially also replace other statement with Nops.
    // Investigate if existing MIR passes do this as part of 'post borrowck cleanup'.
    RemoveFalseEdges.run_pass(tcx, &mut body);
    SimplifyCfg::new("verify").run_pass(tcx, &mut body);

    let (invariants, assertions) = gather.with_corrected_locations_and_names(tcx, &body);
    let func_translator =
        FunctionTranslator::build_context(tcx, ctx, &body, names, invariants, assertions, def_id);

    func_translator.translate()
}

pub fn translate_trusted<'tcx>(
    tcx: TyCtxt<'tcx>,
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> Module {
    let mut names = CloneMap::new(tcx, def_id, true);
    names.clone_self(def_id);
    let mut decls = Vec::new();
    decls.extend(all_generic_decls_for(tcx, def_id));

    let sig = signature_of(ctx, &mut names, def_id);
    let name = module_name(tcx, def_id);

    decls.extend(names.to_clones(ctx));

    decls.push(Decl::ValDecl(ValKind::Val { sig }));
    return Module { name, decls };
}

use crate::resolve::EagerResolver;

// Split this into several sub-contexts: Core, Analysis, Results?
pub struct FunctionTranslator<'body, 'sess, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    def_id: DefId,

    body: &'body Body<'tcx>,

    resolver: EagerResolver<'body, 'tcx>,

    // Spec / Ghost variables
    erased_locals: BitSet<Local>,

    local_map: HashMap<Local, Local>,

    // Current block being generated
    current_block: (Vec<mlcfg::Statement>, Option<mlcfg::Terminator>),

    past_blocks: BTreeMap<mlcfg::BlockId, mlcfg::Block>,

    // Type translation context
    ctx: &'body mut TranslationCtx<'sess, 'tcx>,

    // Fresh BlockId
    fresh_id: usize,

    // Gives a fresh name to every mono-morphization of a function or trait
    clone_names: CloneMap<'tcx>,

    invariants: IndexMap<BasicBlock, Vec<(Symbol, Exp)>>,

    assertions: IndexMap<DefId, Exp>,
    borrows: Rc<BorrowSet<'tcx>>,
}

impl<'body, 'sess, 'tcx> FunctionTranslator<'body, 'sess, 'tcx> {
    fn build_context(
        tcx: TyCtxt<'tcx>,
        ctx: &'body mut TranslationCtx<'sess, 'tcx>,
        body: &'body Body<'tcx>,
        clone_names: CloneMap<'tcx>,
        invariants: IndexMap<BasicBlock, Vec<(Symbol, Exp)>>,
        assertions: IndexMap<DefId, Exp>,
        def_id: DefId,
    ) -> Self {
        let mut erased_locals = BitSet::new_empty(body.local_decls.len());

        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if crate::util::is_spec(tcx, *def_id) {
                    erased_locals.insert(local);
                }
            }
        });

        let mut clean_body = body.clone();

        tcx.infer_ctxt().enter(|infcx| {
            renumber::renumber_mir(&infcx, &mut clean_body, &mut Default::default());
        });
        let move_paths = MoveData::gather_moves(&clean_body, tcx, tcx.param_env(def_id)).unwrap();
        let borrows = BorrowSet::build(tcx, &clean_body, true, &move_paths);
        let local_map = real_locals(tcx, body);
        let borrows = Rc::new(borrows);
        let resolver = EagerResolver::new(tcx, body, borrows.clone());

        FunctionTranslator {
            tcx,
            body,
            def_id,
            resolver,
            erased_locals,
            current_block: (Vec::new(), None),
            past_blocks: BTreeMap::new(),
            ctx,
            fresh_id: body.basic_blocks().len(),
            clone_names,
            invariants,
            assertions,
            local_map,
            borrows,
        }
    }

    fn translate(mut self) -> Module {
        let mut decls: Vec<_> = Vec::new();
        decls.extend(closure_generic_decls(self.tcx, self.def_id));

        if self.tcx.is_closure(self.def_id) {
            if let TyKind::Closure(_, subst) = self.tcx.type_of(self.def_id).kind() {
                let env_ty = Decl::TyDecl(translate_closure_ty(
                    self.ctx,
                    &mut self.clone_names,
                    self.def_id,
                    subst,
                ));
                let accessors = closure_accessors(
                    self.ctx,
                    &mut self.clone_names,
                    self.def_id,
                    subst.as_closure(),
                );
                decls.extend(self.clone_names.to_clones(self.ctx));
                decls.push(env_ty);
                decls.extend(accessors);
            }
        }

        let sig = signature_of(self.ctx, &mut self.clone_names, self.def_id);
        let name = module_name(self.tcx, self.def_id);

        decls.extend(self.clone_names.to_clones(self.ctx));

        if util::is_trusted(self.tcx, self.def_id) {
            decls.push(Decl::ValDecl(ValKind::Val { sig }));
            return Module { name, decls };
        }

        self.translate_body();

        let arg_count = self.body.arg_count;
        let vars = self.translate_vars();

        assert!(self.assertions.is_empty(), "unused assertions");
        assert!(self.invariants.is_empty(), "unused invariants");

        let entry = Block {
            statements: vars
                .iter()
                .skip(1)
                .take(arg_count)
                .map(|(id, _)| {
                    let rhs = id.arg_name();
                    Assign { lhs: id.ident(), rhs: Exp::impure_var(rhs) }
                })
                .collect(),
            terminator: Terminator::Goto(BlockId(0)),
        };
        decls.extend(self.clone_names.to_clones(self.ctx));

        // decls.extend(closure_contract(self.ctx, &mut self.clone_names, self.def_id).into_iter());

        decls.push(Decl::FunDecl(CfgFunction {
            sig,
            vars: vars.into_iter().map(|i| (i.0.ident(), i.1)).collect(),
            entry,
            blocks: self.past_blocks,
        }));
        Module { name, decls }
    }

    fn translate_body(&mut self) {
        for (bb, bbd) in preorder(self.body) {
            self.current_block = (vec![], None);
            if bbd.is_cleanup {
                continue;
            }

            for (name, body) in self.invariants.remove(&bb).unwrap_or_else(Vec::new) {
                self.emit_statement(Invariant(name.to_string().into(), body));
            }

            self.freeze_locals_between_blocks(bb);

            let mut loc = bb.start_location();

            for statement in &bbd.statements {
                self.translate_statement(statement, loc);
                self.freeze_borrows_dying_at(loc);
                loc = loc.successor_within_block();
            }

            self.translate_terminator(bbd.terminator(), loc);

            self.past_blocks.insert(
                BlockId(bb.into()),
                Block {
                    statements: std::mem::take(&mut self.current_block.0),
                    terminator: std::mem::replace(&mut self.current_block.1, None).unwrap(),
                },
            );
        }
    }

    fn translate_vars(&mut self) -> Vec<(LocalIdent, Type)> {
        let mut vars = Vec::with_capacity(self.body.local_decls.len());

        for (loc, decl) in self.body.local_decls.iter_enumerated() {
            if self.erased_locals.contains(loc) {
                continue;
            }
            let ident = self.translate_local(loc);
            vars.push((
                ident,
                ty::translate_ty(
                    &mut self.ctx,
                    &mut self.clone_names,
                    decl.source_info.span,
                    decl.ty,
                ),
            ))
        }

        vars
    }

    fn emit_statement(&mut self, s: mlcfg::Statement) {
        self.current_block.0.push(s);
    }

    fn emit_terminator(&mut self, t: mlcfg::Terminator) {
        assert!(self.current_block.1.is_none());

        self.current_block.1 = Some(t);
    }

    fn emit_assignment(&mut self, lhs: &Place<'tcx>, rhs: mlcfg::Exp) {
        let assign = self.create_assign(lhs, rhs);
        self.emit_statement(assign);
    }

    fn resolve_ty(&mut self, ty: Ty<'tcx>) -> Exp {
        resolve_predicate_of(&mut self.ctx, &mut self.clone_names, self.def_id, ty)
    }

    // Inserts drop statements for variables which died over the course of a goto or switch
    fn freeze_locals_between_blocks(&mut self, bb: BasicBlock) {
        let pred_blocks = &self.body.predecessors()[bb];

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
            if dying.is_empty() {
                continue;
            };

            self.freeze_locals(dying);
            let deaths = std::mem::take(&mut self.current_block.0);

            let drop_block = self.fresh_block_id();
            let pred_id = BlockId(pred.index());

            // Otherwise, we emit the deaths and move them to a stand-alone block.
            self.past_blocks
                .get_mut(&pred_id)
                .unwrap()
                .terminator
                .retarget(BlockId(bb.index()), drop_block);
            self.past_blocks.insert(
                drop_block,
                Block { statements: deaths, terminator: Terminator::Goto(BlockId(bb.into())) },
            );
        }
    }

    fn fresh_block_id(&mut self) -> BlockId {
        let id = BlockId(BasicBlock::from_usize(self.fresh_id).into());
        self.fresh_id += 1;
        id
    }

    fn freeze_borrows_dying_at(&mut self, loc: Location) {
        let dying = self.resolver.locals_resolved_at_loc(loc);
        self.freeze_locals(dying);
    }

    fn freeze_locals(&mut self, mut dying: BitSet<Local>) {
        dying.subtract(&self.erased_locals);

        for local in dying.iter() {
            let local_ty = self.body.local_decls[local].ty;
            let ident = self.translate_local(local).ident();
            let assumption: Exp =
                resolve_predicate_of(&mut self.ctx, &mut self.clone_names, self.def_id, local_ty)
                    .app_to(Exp::impure_var(ident));
            self.emit_statement(mlcfg::Statement::Assume(assumption));
        }
    }

    // Useful helper to translate an operand
    pub fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Exp {
        match operand {
            Operand::Copy(pl) | Operand::Move(pl) => self.translate_rplace(pl),
            Operand::Constant(c) => crate::constant::from_mir_constant(
                &mut self.ctx,
                &mut self.clone_names,
                self.def_id,
                c,
            ),
        }
    }

    fn translate_local(&self, loc: Local) -> LocalIdent {
        use rustc_middle::mir::VarDebugInfoContents::Place;
        let debug_info: Vec<_> = self
            .body
            .var_debug_info
            .iter()
            .filter(|var_info| match var_info.value {
                Place(p) => p.as_local().map(|l| l == loc).unwrap_or(false),
                _ => false,
            })
            .collect();

        assert!(debug_info.len() <= 1, "expected at most one debug entry for local {:?}", loc);

        let loc = self.local_map[&loc];
        match debug_info.get(0) {
            Some(info) => LocalIdent::dbg(loc, *info),
            None => LocalIdent::anon(loc),
        }
    }
}

/// A MIR local along with an optional human-readable name
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LocalIdent(Local, Option<Symbol>);

impl LocalIdent {
    pub fn anon(loc: Local) -> Self {
        LocalIdent(loc, None)
    }

    pub fn dbg(loc: Local, dbg: &VarDebugInfo) -> Self {
        LocalIdent(loc, Some(dbg.name))
    }

    pub fn arg_name(&self) -> why3::Ident {
        match &self.1 {
            None => format!("{:?}'", self.0).into(),
            Some(h) => ident_of(*h),
        }
    }

    pub fn ident(&self) -> why3::Ident {
        match &self.1 {
            Some(id) => format!("{}_{}", &*ident_of(*id), self.0.index()).into(),
            None => format!("_{}", self.0.index()).into(),
        }
    }
}

pub fn closure_contract<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
) -> Vec<Decl> {
    use rustc_middle::ty::{self, ClosureKind::*};
    let subst = match ctx.tcx.type_of(def_id).kind() {
        TyKind::Closure(_, substs) => substs,
        _ => return Vec::new(),
    };
    let kind = subst.as_closure().kind();

    let mut clos_sig = signature_of(ctx, names, def_id);

    // Get the raw contracts
    let contract = names.with_public_clones(|names| {
        contract_of(ctx, def_id).unwrap().check_and_lower(ctx, names, def_id)
    });

    let postcondition = contract.ensures_conj();
    let precondition = contract.requires_conj();

    let result_ty = clos_sig.retty;
    clos_sig.contract = Contract::new();
    clos_sig.retty = None;

    // Build the signatures for the pre and post conditions
    let mut post_sig = clos_sig.clone();
    post_sig.args.push((Ident::build("result"), result_ty.unwrap_or(Type::Tuple(vec![]))));
    let pre_sig = clos_sig;

    let mut contracts = Vec::new();
    let env_ty =
        ctx.tcx.closure_env_ty(def_id, subst, ty::RegionKind::ReErased).unwrap().peel_refs();
    let self_ty = translate_ty(ctx, names, DUMMY_SP, env_ty);

    {
        // Preconditions are the same for every kind of closure
        let mut pre_sig = pre_sig.clone();
        pre_sig.name = Ident::build("precondition");
        pre_sig.args[0].1 = self_ty.clone();
        let mut subst = util::closure_capture_subst(ctx.tcx, names, def_id, subst, FnOnce, true);

        let mut precondition = precondition.clone();
        subst.visit_mut(&mut precondition);

        contracts.push(Decl::PredDecl(Predicate { sig: pre_sig, body: precondition }));
    }

    if kind <= Fn {
        let mut post_sig = post_sig.clone();
        post_sig.name = Ident::build("postcondition");
        post_sig.args[0].1 = self_ty.clone();

        let mut csubst = util::closure_capture_subst(ctx.tcx, names, def_id, subst, Fn, true);
        let mut postcondition = postcondition.clone();

        csubst.visit_mut(&mut postcondition);
        contracts.push(Decl::PredDecl(Predicate { sig: post_sig, body: postcondition }));
    }

    if kind <= FnMut {
        let mut post_sig = post_sig.clone();
        post_sig.name = Ident::build("postcondition_mut");

        let self_ty = Type::MutableBorrow(Box::new(self_ty.clone()));
        post_sig.args[0].1 = self_ty;

        let mut csubst = util::closure_capture_subst(ctx.tcx, names, def_id, subst, FnMut, true);

        let mut postcondition = postcondition.clone();
        postcondition = postcondition.and(closure_unnest(ctx.tcx, names, def_id, subst));

        csubst.visit_mut(&mut postcondition);
        contracts.push(Decl::PredDecl(Predicate { sig: post_sig, body: postcondition }));
    }

    if kind <= FnOnce {
        let mut post_sig = post_sig.clone();
        post_sig.name = Ident::build("postcondition_once");
        post_sig.args[0].1 = self_ty.clone();

        let mut csubst = util::closure_capture_subst(ctx.tcx, names, def_id, subst, FnOnce, true);

        let mut postcondition = postcondition.clone();
        csubst.visit_mut(&mut postcondition);
        contracts.push(Decl::PredDecl(Predicate { sig: post_sig, body: postcondition }));
    }

    contracts.push(closure_resolve(ctx, names, def_id, subst));

    return contracts;
}

fn closure_resolve<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Decl {
    let mut resolve = Exp::mk_true();

    let csubst = subst.as_closure();
    for (ix, ty) in csubst.upvar_tys().enumerate() {
        let acc_name = ty::closure_accessor_name(ctx.tcx, def_id, ix);
        let acc = Exp::impure_qvar(names.insert(def_id, subst).qname_ident(acc_name));
        let self_ = Exp::pure_var(Ident::build("_1'"));

        let resolve_one = resolve_predicate_of(ctx, names, def_id, ty).app_to(acc.app_to(self_));
        resolve = resolve_one.and(resolve);
    }

    let sig = Signature {
        attrs: Vec::new(),
        contract: Contract::new(),
        retty: None,
        name: Ident::build("resolve"),
        args: vec![(
            Ident::build("_1'"),
            translate_ty(ctx, names, ctx.def_span(def_id), ctx.type_of(def_id)),
        )],
    };

    Decl::PredDecl(Predicate { sig, body: resolve })
}

pub fn closure_unnest<'tcx>(
    tcx: TyCtxt<'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Exp {
    let mut unnest = Exp::mk_true();

    let csubst = subst.as_closure();
    for (ix, up_ty) in csubst.upvar_tys().enumerate() {
        if up_ty.is_mutable_ptr() {
            let acc_name = ty::closure_accessor_name(tcx, def_id, ix);
            let acc = Exp::impure_qvar(names.insert(def_id, subst).qname_ident(acc_name));

            let self_ = Exp::pure_var(Ident::build("_1'"));

            let unnest_one = Exp::BinaryOp(
                BinOp::Eq,
                box Exp::Final(box acc.clone().app_to(Exp::Final(box self_.clone()))),
                box Exp::Final(box acc.app_to(Exp::Current(box self_))),
            );

            unnest = unnest_one.and(unnest);
        }
    }

    unnest
}

fn resolve_predicate_of<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
    ty: Ty<'tcx>,
) -> Exp {
    if !resolve_trait_loaded(ctx.tcx) {
        ctx.warn(
            rustc_span::DUMMY_SP,
            "load the `creusot_contract` crate to enable resolution of mutable borrows.",
        );
        return Exp::Abs("x".into(), box Exp::Const(Constant::const_true()));
    }

    let trait_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve")).unwrap();
    let trait_meth_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve_method")).unwrap();
    let subst = ctx.mk_substs([GenericArg::from(ty)].iter());

    let param_env = ctx.param_env(def_id);
    let resolve_impl = traits::resolve_assoc_item_opt(ctx.tcx, param_env, trait_meth_id, subst);

    match resolve_impl {
        Some(method) => {
            ctx.translate(method.0);
            Exp::impure_qvar(names.insert(method.0, method.1).qname(ctx.tcx, method.0))
        }
        None => {
            ctx.translate(trait_id);
            Exp::impure_qvar(names.insert(trait_meth_id, subst).qname(ctx.tcx, trait_meth_id))
        }
    }
}

fn resolve_trait_loaded(tcx: TyCtxt) -> bool {
    tcx.get_diagnostic_item(Symbol::intern("creusot_resolve")).is_some()
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
            def_id = tcx.parent(def_id).unwrap();
        } else {
            break;
        }
    }

    all_generic_decls_for(tcx, def_id)
}

pub fn all_generic_decls_for(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = Decl> + '_ {
    let generics = tcx.generics_of(def_id);

    generic_decls((0..generics.count()).map(move |i| generics.param_at(i, tcx)))
}

pub fn own_generic_decls_for(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = Decl> + '_ {
    let generics = tcx.generics_of(def_id);
    generic_decls(generics.params.iter())
}

fn generic_decls<'tcx, I: Iterator<Item = &'tcx GenericParamDef> + 'tcx>(
    it: I,
) -> impl Iterator<Item = Decl> + 'tcx {
    it.filter_map(|param| {
        if let GenericParamDefKind::Type { .. } = param.kind {
            Some(Decl::TyDecl(TyDecl {
                ty_name: (&*param.name.as_str().to_lowercase()).into(),
                ty_params: vec![],
                kind: TyDeclKind::Opaque,
            }))
        } else {
            None
        }
    })
}

pub fn real_locals<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashMap<Local, Local> {
    let mut spec_local = 0;
    body.local_decls
        .iter_enumerated()
        .filter_map(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if crate::util::is_spec(tcx, *def_id) {
                    spec_local += 1;
                    return None;
                }
            }
            Some((local, (local.index() - spec_local).into()))
        })
        .collect()
}
