use crate::extended_location::*;
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::traversal::preorder,
    mir::{BasicBlock, Body, Local, Location, Operand, VarDebugInfo},
    ty::TyCtxt,
    ty::TyKind,
};

use std::collections::BTreeMap;
use why3::declaration::*;
use why3::mlcfg::{self, Exp::*, Statement::*, *};

use rustc_middle::mir::Place;
use rustc_middle::ty::{GenericParamDef, GenericParamDefKind};

use indexmap::IndexSet;

mod constant;
mod place;
pub mod specification;
mod statement;
mod terminator;
pub mod ty;

pub use constant::*;

use crate::ctx::*;

use self::specification::RustcResolver;

pub fn translate_function<'tcx, 'sess>(
    tcx: TyCtxt<'tcx>,
    ctx: &mut TranslationCtx<'sess, 'tcx>,
    body: &Body<'tcx>,
    def_id: DefId,
    contract: Contract,
) {
    let func_translator = FunctionTranslator::build_context(tcx, ctx, body, def_id);
    let module = func_translator.translate(contract);
    ctx.modules.add_module(module);
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
    clone_names: NameMap<'tcx>,

    imports: IndexSet<QName>,
}

impl<'body, 'sess, 'tcx> FunctionTranslator<'body, 'sess, 'tcx> {
    fn build_context(
        tcx: TyCtxt<'tcx>,
        ctx: &'body mut TranslationCtx<'sess, 'tcx>,
        body: &'body Body<'tcx>,
        def_id: DefId,
    ) -> Self {
        let mut erased_locals = BitSet::new_empty(body.local_decls.len());

        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if specification::is_spec_id(tcx, *def_id).unwrap() {
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
            clone_names: NameMap::new(tcx),
            imports,
        }
    }

    fn translate(mut self, mut contract: Contract) -> Module {
        self.translate_body();
        move_invariants_into_loop(&mut self.past_blocks);

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

        let retty = vars[0].1.clone();
        let args = vars
            .iter()
            .skip(1)
            .take(arg_count)
            .map(|(id, ty)| {
                if let LocalIdent::Anon(u, hmn) = id {
                    let hmn = match hmn {
                        None => Some("o".into()),
                        Some(h) => Some(format!("o_{}", h)),
                    };
                    (LocalIdent::Anon(*u, hmn), ty.clone())
                } else {
                    unreachable!("{:?}", id)
                }
            })
            .collect();

        let entry = Block {
            statements: vars
                .iter()
                .skip(1)
                .take(arg_count)
                .map(|(id, _)| {
                    let rhs = if let LocalIdent::Anon(u, hmn) = id {
                        let hmn = match hmn {
                            None => Some("o".into()),
                            Some(h) => Some(format!("o_{}", h)),
                        };
                        LocalIdent::Anon(*u, hmn)
                    } else {
                        unreachable!()
                    };
                    Assign { lhs: id.clone(), rhs: Exp::Var(rhs) }
                })
                .collect(),
            terminator: Terminator::Goto(BlockId(0)),
        };

        self.imports.extend(contract.qfvs().into_iter().map(|qn| qn.module_name()));

        let mut decls: Vec<_> = all_generic_decls_for(self.tcx, self.def_id).collect();

        for imp in self.imports {
            decls.push(Decl::UseDecl(Use { name: imp }))
        }

        for ((def_id, subst), clone_name) in self.clone_names.into_iter() {
            decls.push(clone_item(self.ctx, def_id, subst, clone_name));
        }

        let name = translate_value_id(self.tcx, self.def_id).module.join("");
        let func_name = QName { module: vec![], name: "impl".into() };

        let sig = Signature { name: func_name, retty: Some(retty), args, contract };

        decls.push(Decl::FunDecl(CfgFunction { sig, vars, entry, blocks: self.past_blocks }));
        Module { name, decls }
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

    fn resolver(&self) -> RustcResolver<'tcx> {
        let module_id = self.tcx.parent_module_from_def_id(self.def_id.expect_local()).to_def_id();
        specification::RustcResolver(self.ctx.resolver.clone(), module_id, self.tcx)
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
            let ident = self.translate_local(local);
            let assumption: Exp = ty::drop_predicate(&mut self.ctx, local_ty).app_to(ident.into());
            self.emit_statement(mlcfg::Statement::Assume(assumption));
        }
    }

    // Useful helper to translate an operand
    pub fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Exp {
        match operand {
            Operand::Copy(pl) | Operand::Move(pl) => self.translate_rplace(pl),
            Operand::Constant(c) => Const(from_mir_constant(self.tcx, c)),
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
            Some(info) => mk_anon_dbg(loc, info),
            None => mk_anon(loc),
        }
    }
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

// Translate functions that are external to the crate as opaque values
struct Extern;

impl Extern {
    fn translate(ctx: &mut TranslationCtx, def_id: DefId, span: rustc_span::Span) {
        if !ctx.translated_funcs.insert(def_id) {
            return;
        }

        let sig = ctx.tcx.normalize_erasing_late_bound_regions(
            rustc_middle::ty::ParamEnv::reveal_all(),
            ctx.tcx.fn_sig(def_id),
        );
        let names = ctx.tcx.fn_arg_names(def_id);

        let mut contract = Contract::new();

        // If the return type of the function is ! then add an impossible post-condition
        if sig.output().is_never() {
            contract.ensures.push(Exp::Const(Constant::const_false()));
        }

        let name = translate_value_id(ctx.tcx, def_id).module.join("");

        let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();
        decls.push(Decl::ValDecl(Val {
            sig: Signature {
                name: QName::from_string("impl").unwrap(),
                retty: Some(ty::translate_ty(ctx, span, sig.output())),
                args: names
                    .iter()
                    .zip(sig.inputs())
                    .map(|(id, ty)| (id.name.to_string().into(), ty::translate_ty(ctx, span, ty)))
                    .collect(),
                contract,
            },
        }));

        ctx.modules.add_module(Module { name, decls });
    }
}

fn all_generic_decls_for<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> impl Iterator<Item = Decl> + 'tcx {
    let generics = tcx.generics_of(def_id);

    generic_decls((0..generics.count()).map(move |i| generics.param_at(i, tcx)))
}

fn own_generic_decls_for<'tcx>(
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
                ty_constructors: vec![],
            }))
        } else {
            None
        }
    })
}

fn mk_anon(l: Local) -> LocalIdent {
    LocalIdent::Anon(l.index(), None)
}

fn mk_anon_dbg(l: Local, vi: &VarDebugInfo) -> LocalIdent {
    LocalIdent::Anon(l.index(), Some(vi.name.to_string()))
}
