use crate::extended_location::*;
use crate::module_tree::ModuleTree;
use indexmap::IndexSet;
use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_hir::definitions::DefPathData;
use rustc_index::bit_set::BitSet;
use rustc_middle::{
    mir::traversal::preorder,
    mir::{BasicBlock, Body, Local, Location, Operand, VarDebugInfo},
    ty::TyCtxt,
    ty::TyKind,
};
use rustc_mir::dataflow::{
    self,
    impls::{MaybeInitializedLocals, MaybeLiveLocals},
    Analysis,
};
use rustc_resolve::Namespace;
use rustc_session::Session;
use rustc_span::Span;
use std::collections::BTreeMap;
use why3::declaration::*;
use why3::mlcfg::{self, Exp::*, Pattern::*, Statement::*, *};

use rustc_middle::mir::Place;

pub mod specification;
mod statement;
mod terminator;
pub mod ty;

pub struct TranslationCtx<'sess, 'tcx> {
    sess: &'sess Session,
    tcx: TyCtxt<'tcx>,
    used_tys: IndexSet<DefId>,

    pub modules: ModuleTree,
}

impl<'tcx, 'sess> TranslationCtx<'sess, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'sess Session) -> Self {
        Self { sess, tcx, used_tys: IndexSet::new(), modules: ModuleTree::new() }
    }

    fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub fn add_type(&mut self, ty_decl: TyDecl, drop_pred: Predicate) {
        let mut dependencies = ty_decl.used_types();
        let type_ns = QName::from_string("Type").unwrap();
        let module = self.modules.get_module_mut(type_ns);

        let mut pos = 0;
        while !dependencies.is_empty() && pos < module.len() {
            match &module[pos] {
                TyDecl(tyd) => {
                    dependencies.remove(&tyd.ty_name);
                }
                _ => {}
            }

            pos += 2;
        }
        use why3::declaration::Decl::*;
        module.insert(pos, PredDecl(drop_pred));
        module.insert(pos, TyDecl(ty_decl));
    }
}

// Split this into several sub-contexts: Core, Analysis, Results?
pub struct FunctionTranslator<'body, 'sess, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    body: &'body Body<'tcx>,

    local_live: dataflow::ResultsCursor<'body, 'tcx, MaybeLiveLocals>,

    // Whether a local is initialized or not at a location
    local_init: dataflow::ResultsCursor<'body, 'tcx, MaybeInitializedLocals>,

    // Locals that are never read
    never_live: BitSet<Local>,

    // Spec / Ghost variables
    erased_locals: BitSet<Local>,

    // Current block being generated
    current_block: (Vec<mlcfg::Statement>, Option<mlcfg::Terminator>),

    past_blocks: BTreeMap<mlcfg::BlockId, mlcfg::Block>,

    // Type translation context
    ctx: &'body mut TranslationCtx<'sess, 'tcx>,

    // Name resolution context for specs
    resolver: crate::specification::RustcResolver<'tcx>,

    // Fresh BlockId
    fresh_id: usize,
}

impl<'body, 'sess, 'tcx> FunctionTranslator<'body, 'sess, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        ctx: &'body mut TranslationCtx<'sess, 'tcx>,
        body: &'body Body<'tcx>,
        resolver: specification::RustcResolver<'tcx>,
    ) -> Self {
        let local_init = MaybeInitializedLocals
            .into_engine(tcx, &body)
            .iterate_to_fixpoint()
            .into_results_cursor(&body);

        // This is called MaybeLiveLocals because pointers don't keep their referees alive.
        // TODO: Defensive check.
        let local_live = MaybeLiveLocals
            .into_engine(tcx, &body)
            .iterate_to_fixpoint()
            .into_results_cursor(&body);

        let mut erased_locals = BitSet::new_empty(body.local_decls.len());

        body.local_decls.iter_enumerated().for_each(|(local, decl)| {
            if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
                if specification::is_spec_id(tcx, *def_id).unwrap() {
                    erased_locals.insert(local);
                }
            }
        });

        let never_live = crate::analysis::NeverLive::for_body(body);
        warn!("ever_live_set: {:?}", never_live);
        FunctionTranslator {
            tcx,
            body,
            local_live,
            local_init,
            erased_locals,
            never_live,
            current_block: (Vec::new(), None),
            past_blocks: BTreeMap::new(),
            ctx,
            resolver,
            fresh_id: body.basic_blocks().len(),
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

    pub fn translate(mut self, nm: DefId, contracts: Contract) -> CfgFunction {
        self.translate_body();

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

        let name = translate_value_id(self.tcx, nm);

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

        move_invariants_into_loop(&mut self.past_blocks);

        let sig = Signature { name, retty: Some(retty), args, contract: contracts };
        CfgFunction { sig, vars, entry, blocks: self.past_blocks }
    }

    fn translate_body(&mut self) {
        for (bb, bbd) in preorder(self.body) {
            self.current_block = (vec![], None);
            if bbd.is_cleanup {
                continue;
            }
            self.drop_variables_between_blocks(bb);

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
                    statements: std::mem::replace(&mut self.current_block.0, Vec::new()),
                    terminator: std::mem::replace(&mut self.current_block.1, None).unwrap(),
                },
            );
        }
    }

    // Inserts drop statements for variables which died over the course of a goto or switch
    fn drop_variables_between_blocks(&mut self, bb: BasicBlock) {
        use ExtendedLocation::*;

        let pred_blocks = &self.body.predecessors()[bb];
        if pred_blocks.is_empty() {
            return;
        }

        let term_loc = self.body.terminator_loc(pred_blocks[0]);
        self.local_live.seek_before_primary_effect(term_loc);
        let live_in_bb = self.local_live.get().clone();

        for pred in pred_blocks {
            let term_loc = self.body.terminator_loc(*pred);
            self.local_live.seek_before_primary_effect(term_loc);
            let live_at_term = self.local_live.get();

            // If nothing died in the block transition we can just skip emitting a death block
            if &live_in_bb == live_at_term {
                continue;
            }

            self.freeze_borrows_dying_between(Start(term_loc), Start(bb.start_location()));
            let deaths = std::mem::replace(&mut self.current_block.0, Vec::new());

            let drop_block = self.fresh_block_id();
            let pred_id = BlockId(pred.index());
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
        self.freeze_borrows_dying_between(Start(term_loc), Start(bb.start_location()));
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
        start.seek_to(&mut self.local_live);
        let mut live_at_start = self.local_live.get().clone();
        if start.is_entry_loc() {
            // Count arguments that were never live as live here
            live_at_start.union(&self.never_live);
        }

        end.seek_to(&mut self.local_live);
        let live_at_end = self.local_live.get();

        start.seek_to(&mut self.local_init);
        let init_at_start = self.local_init.get().clone();

        end.seek_to(&mut self.local_init);
        let init_at_end = self.local_init.get().clone();

        debug!("location: {:?}-{:?}", start, end);
        debug!("live_at_start: {:?}", live_at_start);
        debug!("live_at_end: {:?}", live_at_end);
        debug!("init_at_start: {:?}", init_at_start);
        debug!("init_at_end: {:?}", init_at_end);
        debug!("erased_locals: {:?}", self.erased_locals);

        // Locals that were just now initialized
        let mut just_init = init_at_end.clone();
        just_init.subtract(&init_at_start);

        // Locals that have just become live
        let mut born = live_at_end.clone();
        born.subtract(&live_at_start);

        // Locals that were initialized but never live
        let mut zombies = just_init.clone();
        zombies.subtract(live_at_end);

        let mut dying = live_at_start;

        // Variables that died in the span
        dying.subtract(live_at_end);
        // And were initialized
        dying.intersect(&init_at_start);
        // But if we created a new value or brought one back to life
        if !just_init.is_empty() || !born.is_empty() {
            // Exclude values that were moved
            dying.intersect(&init_at_end);
            // And include the values that never made it past their creation
            dying.union(&zombies);
        }
        // Ignore spec stuff
        dying.subtract(&self.erased_locals);

        debug!("dying: {:?}", dying);

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

    pub fn translate_rplace(&mut self, rhs: &Place<'tcx>) -> Exp {
        self.translate_rplace_inner(rhs.local, rhs.projection)
    }

    // [(P as Some)]   ---> [_1]
    // [(P as Some).0] ---> let Some(a) = [_1] in a
    // [(* P)] ---> * [P]
    fn translate_rplace_inner(
        &mut self,
        loc: Local,
        proj: &[rustc_middle::mir::PlaceElem<'tcx>],
    ) -> Exp {
        let mut inner = self.translate_local(loc).into();
        use rustc_middle::mir::ProjectionElem::*;
        let mut place_ty = Place::ty_from(loc, &[], self.body, self.tcx);

        for elem in proj {
            match elem {
                Deref => {
                    use rustc_hir::Mutability::*;
                    let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                    if mutability == Mut {
                        inner = Current(box inner)
                    }
                }
                Field(ix, _) => match place_ty.ty.kind() {
                    TyKind::Adt(def, _) => {
                        let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                        let variant = &def.variants[variant_id];

                        let mut pat = vec![Wildcard; variant.fields.len()];
                        pat[ix.as_usize()] = VarP("a".into());

                        let tyname = translate_value_id(self.tcx, variant.def_id);

                        inner = Let {
                            pattern: ConsP(tyname, pat),
                            arg: box inner,
                            body: box Var("a".into()),
                        }
                    }
                    TyKind::Tuple(fields) => {
                        let mut pat = vec![Wildcard; fields.len()];
                        pat[ix.as_usize()] = VarP("a".into());

                        inner =
                            Let { pattern: TupleP(pat), arg: box inner, body: box Var("a".into()) }
                    }
                    _ => unreachable!(),
                },
                Downcast(_, _) => {}
                _ => unimplemented!("unimplemented place projection"),
            }
            place_ty = place_ty.projection_ty(self.tcx, *elem);
        }

        inner
    }

    /// Correctly translate an assignment from one place to another. The challenge here is correctly
    /// construction the expression that assigns deep inside a structure.
    /// (_1 as Some) = P      ---> let _1 = P ??
    /// (*_1) = P             ---> let _1 = { current = P, .. }
    /// (_1.2) = P            ---> let _1 = { _1 with [[2]] = P } (struct)
    ///                       ---> let _1 = (let Cons(a, b, c) = _1 in Cons(a, b, P)) (tuple)
    /// (*_1).1 = P           ---> let _1 = { _1 with current = ({ * _1 with [[1]] = P })}
    /// ((*_1) as Some).0 = P ---> let _1 = { _1 with current = (let Some(X) = _1 in Some(P) )}

    /// [(_1 as Some).0] = X   ---> let _1 = (let Some(a) = _1 in Some(X))
    /// (* (* _1).2) = X ---> let _1 = { _1 with current = { * _1 with current = [(**_1).2 = X] }}
    pub fn create_assign(&mut self, lhs: &Place<'tcx>, rhs: Exp) -> mlcfg::Statement {
        // Translation happens inside to outside, which means we scan projection elements in reverse
        // building up the inner expression. We start with the RHS expression which is at the deepest
        // level.

        let mut inner = rhs;

        // Each level of the translation needs access to the _previous_ value at this nesting level
        // So we track the path from the root as we traverse, which we call the stump.
        let mut stump: &[_] = lhs.projection.clone();

        use rustc_middle::mir::ProjectionElem::*;

        for (proj, elem) in lhs.iter_projections().rev() {
            // twisted stuff
            stump = &stump[0..stump.len() - 1];
            let place_ty = proj.ty(self.body, self.tcx);

            match elem {
                Deref => {
                    use rustc_hir::Mutability::*;

                    let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                    if mutability == Mut {
                        inner = RecUp {
                            record: box self.translate_rplace_inner(lhs.local, stump),
                            label: "current".into(),
                            val: box inner,
                        }
                    }
                }
                Field(ix, _) => match place_ty.ty.kind() {
                    TyKind::Adt(def, _) => {
                        let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                        let variant = &def.variants[variant_id];
                        let var_size = variant.fields.len();

                        let field_pats = ('a'..)
                            .map(|c| VarP(LocalIdent::Name(c.to_string())))
                            .take(var_size)
                            .collect();
                        let mut varexps: Vec<Exp> =
                            ('a'..).map(|c| Var(c.to_string().into())).take(var_size).collect();

                        varexps[ix.as_usize()] = inner;

                        let tyname = translate_value_id(self.tcx, variant.def_id);

                        inner = Let {
                            pattern: ConsP(tyname.clone(), field_pats),
                            arg: box self.translate_rplace_inner(lhs.local, stump),
                            body: box Constructor { ctor: tyname, args: varexps },
                        }
                    }
                    TyKind::Tuple(fields) => {
                        let var_size = fields.len();

                        let field_pats = ('a'..)
                            .map(|c| VarP(LocalIdent::Name(c.to_string())))
                            .take(var_size)
                            .collect();
                        let mut varexps: Vec<Exp> =
                            ('a'..).map(|c| Var(c.to_string().into())).take(var_size).collect();

                        varexps[ix.as_usize()] = inner;

                        inner = Let {
                            pattern: TupleP(field_pats),
                            arg: box self.translate_rplace_inner(lhs.local, stump),
                            body: box Tuple(varexps),
                        }
                    }
                    _ => unreachable!(),
                },
                Downcast(_, _) => {}
                _ => unimplemented!(),
            }
        }

        let ident = self.translate_local(lhs.local);
        Assign { lhs: ident, rhs: inner }
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

use heck::{CamelCase, MixedCase};

pub fn translate_type_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, true)
}

pub fn translate_value_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, false)
}

fn translate_defid(tcx: TyCtxt, def_id: DefId, ty: bool) -> QName {
    let def_path = tcx.def_path(def_id);

    let mut mod_segs = Vec::new();
    let mut name_segs = Vec::new();

    if def_path.krate.as_u32() != 0 {
        mod_segs.push(tcx.crate_name(def_id.krate).to_string())
    }

    for seg in def_path.data[..].iter() {
        match seg.data {
            // DefPathData::CrateRoot => mod_segs.push(tcx.crate_name(def_id.krate).to_string()),
            DefPathData::TypeNs(_) => mod_segs.push(format!("{}", seg)[..].to_camel_case()),
            // CORE ASSUMPTION: Once we stop seeing TypeNs we never see it again.
            DefPathData::Ctor => {}
            _ => name_segs.push(format!("{}", seg)[..].to_mixed_case()),
        }
    }

    let kind = tcx.def_kind(def_id);
    use rustc_hir::def::DefKind::*;

    match (kind, kind.ns()) {
        (_, _) if ty => {
            assert_eq!(name_segs.len(), 0);
            name_segs = mod_segs.into_iter().map(|seg| seg.to_lowercase()).collect();
            mod_segs = vec!["Type".to_owned()];
        }
        (Ctor(_, _) | Variant | Struct, _) => {
            mod_segs.append(&mut name_segs);
            mod_segs[0] = mod_segs[0].to_camel_case();
            name_segs = mod_segs;
            mod_segs = vec!["Type".to_owned()];
        }
        (Mod, _) => {}
        (_, Some(Namespace::ValueNS)) => {}
        (_, _) => unreachable!(),
    }

    QName { module: mod_segs, name: name_segs.join("_") }
}

fn mk_anon(l: Local) -> LocalIdent {
    LocalIdent::Anon(l.index(), None)
}
fn mk_anon_dbg(l: Local, vi: &VarDebugInfo) -> LocalIdent {
    LocalIdent::Anon(l.index(), Some(vi.name.to_string()))
}

pub fn from_mir_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    c: &rustc_middle::mir::Constant<'tcx>,
) -> mlcfg::Constant {
    use rustc_middle::ty::TyKind::{Int, Uint};
    use rustc_middle::ty::{IntTy::*, UintTy::*};
    use rustc_target::abi::Size;

    match c.literal.ty().kind() {
        Int(I8) => Constant::Int(
            c.literal.try_to_bits(Size::from_bytes(1)).unwrap() as i128,
            Some(ty::i8_ty()),
        ),
        Int(I16) => Constant::Int(
            c.literal.try_to_bits(Size::from_bytes(2)).unwrap() as i128,
            Some(ty::i16_ty()),
        ),
        Int(I32) => Constant::Int(
            c.literal.try_to_bits(Size::from_bytes(4)).unwrap() as i128,
            Some(ty::i32_ty()),
        ),
        Int(I64) => Constant::Int(
            c.literal.try_to_bits(Size::from_bytes(8)).unwrap() as i128,
            Some(ty::i64_ty()),
        ),
        Int(I128) => unimplemented!("128-bit integers are not supported"),

        Uint(U8) => {
            Constant::Uint(c.literal.try_to_bits(Size::from_bytes(1)).unwrap(), Some(ty::u8_ty()))
        }
        Uint(U16) => {
            Constant::Uint(c.literal.try_to_bits(Size::from_bytes(2)).unwrap(), Some(ty::u16_ty()))
        }
        Uint(U32) => {
            Constant::Uint(c.literal.try_to_bits(Size::from_bytes(4)).unwrap(), Some(ty::u32_ty()))
        }
        Uint(U64) => {
            Constant::Uint(c.literal.try_to_bits(Size::from_bytes(8)).unwrap(), Some(ty::u64_ty()))
        }
        Uint(U128) => {
            unimplemented!("128-bit integers are not supported")
        }
        Uint(Usize) => Constant::Uint(
            c.literal.try_to_bits(Size::from_bytes(8)).unwrap(),
            Some(ty::usize_ty()),
        ),
        _ => {
            use rustc_middle::ty::print::{FmtPrinter, PrettyPrinter};
            let mut fmt = String::new();
            let cx = FmtPrinter::new(tcx, &mut fmt, Namespace::ValueNS);
            // cx.pretty_print_const(c.literal, false).unwrap();
            use rustc_middle::mir::ConstantKind;
            match c.literal {
                ConstantKind::Ty(c) => cx.pretty_print_const(c, false).unwrap(),
                ConstantKind::Val(val, ty) => cx.pretty_print_const_value(val, ty, false).unwrap(),
            };

            Constant::Other(fmt)
        }
    }
}
