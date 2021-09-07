use crate::{extended_location::*, util::signature_of};
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::traversal::preorder,
    mir::{visit::MutVisitor, BasicBlock, Body, Local, Location, Operand, VarDebugInfo},
    ty::TyCtxt,
    ty::{TyKind, WithOptConstParam},
};
use std::collections::BTreeMap;
use why3::declaration::*;
use why3::mlcfg::{self, Exp::*, Statement::*, *};
use why3::QName;

use rustc_middle::mir::Place;
use rustc_middle::ty::subst::GenericArg;
use rustc_middle::ty::Ty;
use rustc_middle::ty::{GenericParamDef, GenericParamDefKind};
use rustc_resolve::Namespace;
use rustc_span::Symbol;

use indexmap::{IndexMap, IndexSet};

mod place;
mod statement;
mod terminator;

use crate::ctx::*;
use crate::translation::specification;
use crate::translation::{traits, ty};

pub fn translate_function<'tcx, 'sess>(
    tcx: TyCtxt<'tcx>,
    ctx: &mut TranslationCtx<'sess, 'tcx>,
    def_id: DefId,
) -> Module {
    let mut names = CloneMap::with_self_ref(tcx, def_id);
    let invariants = specification::gather_invariants(ctx, &mut names, def_id);
    let (body, _) = tcx.mir_promoted(WithOptConstParam::unknown(def_id.expect_local()));
    let mut body = body.borrow().clone();
    // Basic clean up, replace FalseEdges with Gotos. Could potentially also replace other statement with Nops.
    // Investigate if existing MIR passes do this as part of 'post borrowck cleanup'.
    RemoveFalseEdge { tcx }.visit_body(&mut body);

    let func_translator =
        FunctionTranslator::build_context(tcx, ctx, &body, names, invariants, def_id);
    let module = func_translator.translate();
    module
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

    // Current block being generated
    current_block: (Vec<mlcfg::Statement>, Option<mlcfg::Terminator>),

    past_blocks: BTreeMap<mlcfg::BlockId, mlcfg::Block>,

    // Type translation context
    ctx: &'body mut TranslationCtx<'sess, 'tcx>,

    // Fresh BlockId
    fresh_id: usize,

    // Gives a fresh name to every mono-morphization of a function or trait
    clone_names: CloneMap<'tcx>,

    imports: IndexSet<QName>,

    invariants: IndexMap<DefId, Exp>,
}

impl<'body, 'sess, 'tcx> FunctionTranslator<'body, 'sess, 'tcx> {
    fn build_context(
        tcx: TyCtxt<'tcx>,
        ctx: &'body mut TranslationCtx<'sess, 'tcx>,
        body: &'body Body<'tcx>,
        clone_names: CloneMap<'tcx>,
        invariants: IndexMap<DefId, Exp>,
        def_id: DefId,
    ) -> Self {
        let mut erased_locals = BitSet::new_empty(body.local_decls.len());

        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if crate::util::is_invariant(tcx, *def_id) {
                    erased_locals.insert(local);
                }
            }
        });

        let resolver = EagerResolver::new(tcx, body);
        let imports = IndexSet::new();

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
            imports,
            invariants,
        }
    }

    fn translate(mut self) -> Module {
        self.translate_body();
        move_invariants_into_loop(&mut self.past_blocks);

        let pre_contract = specification::contract_of(self.tcx, self.def_id).unwrap();
        let mut contract =
            pre_contract.check_and_lower(&mut self.ctx, &mut self.clone_names, self.def_id);
        let subst = specification::subst_for_arguments(self.body);

        contract.subst(&subst);
        contract.extend(self.trait_contract().unwrap_or_else(Contract::new));

        let arg_count = self.body.arg_count;
        let vars: Vec<_> = self
            .body
            .local_decls
            .iter_enumerated()
            .filter_map(|(loc, decl)| {
                if self.erased_locals.contains(loc) {
                    None
                } else {
                    let ident = self.translate_local(loc);
                    Some((ident, ty::translate_ty(&mut self.ctx, decl.source_info.span, decl.ty)))
                }
            })
            .collect();

        if self.body.local_decls[0u32.into()].ty.is_never() {
            contract.ensures.push(Exp::Const(Constant::const_false()));
        }

        let entry = Block {
            statements: vars
                .iter()
                .skip(1)
                .take(arg_count)
                .map(|(id, _)| {
                    let rhs = id.arg_name();
                    Assign { lhs: id.ident(), rhs: rhs.into() }
                })
                .collect(),
            terminator: Terminator::Goto(BlockId(0)),
        };

        let mut decls: Vec<_> = super::prelude_imports(true);
        decls.extend(all_generic_decls_for(self.tcx, self.def_id));

        for imp in self.imports {
            decls.push(Decl::UseDecl(Use { name: imp }))
        }

        for tp in traits::traits_used_by(self.tcx, self.def_id) {
            traits::translate_constraint(self.ctx, &mut self.clone_names, tp);
        }

        let sig = signature_of(self.ctx, &mut self.clone_names, self.def_id);
        decls.extend(self.clone_names.to_clones(self.ctx));

        let name = translate_value_id(self.tcx, self.def_id);

        // let sig = Signature { name: name.name.clone().into(), retty: Some(retty), args, contract };
        decls.push(Decl::FunDecl(CfgFunction { sig, vars: vars.into_iter().map(|i| (i.0.ident(), i.1)).collect(), entry, blocks: self.past_blocks }));
        Module { name: name.module_name().name, decls }
    }

    fn translate_body(&mut self) {
        for (bb, bbd) in preorder(self.body) {
            self.current_block = (vec![], None);
            if bbd.is_cleanup {
                continue;
            }
            self.freeze_locals_between_blocks(bb);

            let mut loc = bb.start_location();
            for statement in &bbd.statements {
                self.translate_statement(statement);
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

    fn trait_contract(&mut self) -> Option<Contract> {
        let trait_method_item = self
            .tcx
            .impl_of_method(self.def_id)
            .and_then(|impl_id| self.tcx.trait_id_of_impl(impl_id))
            .and_then(|trait_id| {
                let assoc = self.tcx.associated_item(self.def_id);
                self.tcx.associated_items(trait_id).find_by_name_and_namespace(
                    self.tcx,
                    assoc.ident,
                    Namespace::ValueNS,
                    trait_id,
                )
            })?;

        let pre_contract =
            crate::specification::contract_of(self.ctx.tcx, trait_method_item.def_id).unwrap();
        Some(pre_contract.check_and_lower(
            self.ctx,
            &mut self.clone_names,
            trait_method_item.def_id,
        ))
    }

    fn resolve_predicate_of(&mut self, ty: Ty<'tcx>) -> Exp {
        if !resolve_trait_loaded(self.tcx) {
            self.ctx.warn(
                rustc_span::DUMMY_SP,
                "load the `creusot_contract` crate to enable resolution of mutable borrows.",
            );
            return Exp::Abs("x".into(), box Exp::Const(Constant::const_true()));
        }

        let trait_id = self.tcx.get_diagnostic_item(Symbol::intern("creusot_resolve")).unwrap();
        let trait_meth_id =
            self.tcx.get_diagnostic_item(Symbol::intern("creusot_resolve_method")).unwrap();
        let subst = self.tcx.mk_substs([GenericArg::from(ty)].iter());

        let instance = traits::resolve_instance_opt(self.tcx, self.def_id, trait_meth_id, subst);

        match instance {
            Some(Some(inst)) => {
                traits::translate_impl(self.ctx, self.tcx.impl_of_method(inst.def_id()).unwrap());

                QVar(self.clone_names.qname_for(inst.def_id(), inst.substs))
            }
            _ => {
                self.ctx.translate_trait(trait_id);
                let clone_name = self.clone_names.name_for(trait_id, subst);
                QVar(QName { module: vec![clone_name], name: "resolve".into() })
            }
        }
    }

    // Inserts drop statements for variables which died over the course of a goto or switch
    fn freeze_locals_between_blocks(&mut self, bb: BasicBlock) {
        use ExtendedLocation::*;

        let pred_blocks = &self.body.predecessors()[bb];

        if pred_blocks.is_empty() {
            return;
        }

        let term_loc = self.body.terminator_loc(pred_blocks[0]);
        let dying_in_first =
            self.resolver.locals_resolved_between(Start(term_loc), Start(bb.start_location()));
        let mut same_deaths = true;

        // If we have multiple predecessors (join point) but all of them agree on the deaths, then don't introduce a dedicated block.
        for pred in pred_blocks {
            let term_loc = self.body.terminator_loc(*pred);
            let dying =
                self.resolver.locals_resolved_between(Start(term_loc), Start(bb.start_location()));
            same_deaths = same_deaths && dying_in_first == dying
        }

        if same_deaths {
            self.freeze_borrows_dying_between(Start(term_loc), Start(bb.start_location()));
            return;
        }

        for pred in pred_blocks {
            let term_loc = self.body.terminator_loc(*pred);
            let dying =
                self.resolver.locals_resolved_between(Start(term_loc), Start(bb.start_location()));

            // If no deaths occured in block transition then skip entirely
            if dying.is_empty() {
                continue;
            };

            self.freeze_borrows_dying_between(Start(term_loc), Start(bb.start_location()));
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
        use ExtendedLocation::*;
        self.freeze_borrows_dying_between(Start(loc), Mid(loc));
    }

    fn freeze_borrows_dying_between(&mut self, start: ExtendedLocation, end: ExtendedLocation) {
        let mut dying = self.resolver.locals_resolved_between(start, end);
        dying.subtract(&self.erased_locals);

        for local in dying.iter() {
            let local_ty = self.body.local_decls[local].ty;
            let ident = self.translate_local(local).ident();
            let assumption: Exp = self.resolve_predicate_of(local_ty).app_to(ident.into());
            self.emit_statement(mlcfg::Statement::Assume(assumption));
        }
    }

    // Useful helper to translate an operand
    pub fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Exp {
        match operand {
            Operand::Copy(pl) | Operand::Move(pl) => self.translate_rplace(pl),
            Operand::Constant(c) => Const(crate::constant::from_mir_constant(self.tcx, c)),
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

        match debug_info.get(0) {
            Some(info) => LocalIdent::dbg(loc, *info),
            None => LocalIdent::anon(loc),
        }
    }
}

/// A MIR local along with an optional human-readable name
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LocalIdent(Local, Option<String>);

impl LocalIdent {
    pub fn anon(loc: Local) -> Self {
        LocalIdent(loc, None)
    }

    pub fn dbg(loc: Local, dbg: &VarDebugInfo) -> Self {
        LocalIdent(loc, Some(dbg.name.to_string()))
    }

    pub fn arg_name(&self) -> why3::Ident {
        match &self.1 {
            None => format!("{:?}", self.0).into(),
            Some(h) => h.clone().into(),
        }
    }

    pub fn ident(&self) -> why3::Ident {
        match &self.1 {
            Some(id) => format!("{}_{}", id, self.0.index()).into(),
            None => format!("_{}", self.0.index()).into(),
        }
    }
}

fn resolve_trait_loaded(tcx: TyCtxt) -> bool {
    tcx.get_diagnostic_item(Symbol::intern("creusot_resolve")).is_some()
}

fn move_invariants_into_loop(body: &mut BTreeMap<BlockId, Block>) {
    // CORRECTNESS: We assume that invariants are placed at the end of the block entering into the loop.
    // This is enforced syntactically at source level using macros, however it could get broken during
    // compilation.
    let mut changes = std::collections::HashMap::new();
    for (_, block) in body.iter_mut() {
        let (invariants, rest) =
            block.statements.clone().into_iter().partition(|stmt| matches!(stmt, Invariant(_, _)));

        let _ = std::mem::replace(&mut block.statements, rest);
        if !invariants.is_empty() {
            if let mlcfg::Terminator::Goto(tgt) = &block.terminator {
                changes.insert(*tgt, invariants);
            } else {
                panic!("BAD INVARIANT BAD!")
            }
        }
    }

    for (tgt, mut invs) in changes.drain() {
        let tgt = body.get_mut(&tgt).unwrap();
        invs.append(&mut tgt.statements);
        let _ = std::mem::replace(&mut tgt.statements, invs);
    }
}

pub fn all_generic_decls_for<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> impl Iterator<Item = Decl> + 'tcx {
    let generics = tcx.generics_of(def_id);

    generic_decls((0..generics.count()).map(move |i| generics.param_at(i, tcx)))
}

#[allow(dead_code)]
pub fn own_generic_decls_for<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> impl Iterator<Item = Decl> + 'tcx {
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

struct RemoveFalseEdge<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for RemoveFalseEdge<'tcx> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(
        &mut self,
        terminator: &mut rustc_middle::mir::Terminator<'tcx>,
        _location: Location,
    ) {
        if let rustc_middle::mir::TerminatorKind::FalseEdge { real_target, .. } = terminator.kind {
            terminator.kind = rustc_middle::mir::TerminatorKind::Goto { target: real_target }
        }
    }
}
