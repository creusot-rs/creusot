use std::collections::BTreeMap;

use crate::def_path_trie::DefPathTrie;
use crate::place::Mutability as M;
use crate::{
    place::simplify_place,
    place::{Mutability::*, Projection::*, SimplePlace},
};
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
    Analysis
};
use why3::mlcfg::{self, Exp::*, Pattern::*, Statement::*, *};
use crate::extended_location::*;

use rustc_resolve::Namespace;
use rustc_session::Session;

pub mod specification;
mod statement;
mod terminator;
pub mod ty;
pub mod util;

pub struct TranslatedCrate {
    pub name: String,
    types: Vec<(TyDecl, Predicate)>,
    // TODO: Hide this
    pub modules: DefPathTrie<Module>,
}

impl TranslatedCrate {
    pub fn new(name: String) -> Self {
        TranslatedCrate {
            name: name.to_camel_case(),
            types: Vec::new(),
            modules: DefPathTrie::new(),
        }
    }

    pub fn types(&self) -> impl Iterator<Item = &(TyDecl, Predicate)> {
        self.types.iter()
    }

    pub fn add_type(&mut self, ty_decl: TyDecl, drop_pred: Predicate) {
        let mut dependencies = ty_decl.used_types();
        let mut pos = 0;
        while !dependencies.is_empty() && pos < self.types.len() {
            dependencies.remove(&self.types[0].0.ty_name);
            pos += 1;
        }
        self.types.insert(pos, (ty_decl, drop_pred));
    }
}

// Split this into several sub-contexts: Core, Analysis, Results?
pub struct FunctionTranslator<'a, 'b, 'tcx> {
    sess: &'a Session,
    pub tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,

    local_live: dataflow::ResultsCursor<'a, 'tcx, MaybeLiveLocals>,

    // Whether a local is initialized or not at a location
    local_init: dataflow::ResultsCursor<'a, 'tcx, MaybeInitializedLocals>,

    // Locals that are never read
    never_live: BitSet<Local>,

    // Spec / Ghost variables
    erased_locals: BitSet<Local>,

    // Current block being generated
    current_block: (Vec<mlcfg::Statement>, Option<mlcfg::Terminator>),

    past_blocks: BTreeMap<mlcfg::BlockId, mlcfg::Block>,

    // Type translation context
    ty_ctx: &'a mut ty::Ctx<'b, 'tcx>,

    // Name resolution context for specs
    resolver: crate::specification::RustcResolver<'tcx>,
}



impl<'a, 'b, 'tcx> FunctionTranslator<'a, 'b, 'tcx> {
    pub fn new(
        sess: &'a Session,
        tcx: TyCtxt<'tcx>,
        ctx: &'a mut ty::Ctx<'b, 'tcx>,
        body: &'a Body<'tcx>,
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
            sess,
            tcx,
            body,
            local_live,
            local_init,
            erased_locals,
            never_live,
            current_block: (Vec::new(), None),
            past_blocks: BTreeMap::new(),
            ty_ctx: ctx,
            resolver,
        }
    }

    fn emit_statement(&mut self, s: mlcfg::Statement) {
        self.current_block.0.push(s);
    }

    fn emit_terminator(&mut self, t: mlcfg::Terminator) {
        assert!(self.current_block.1.is_none());

        self.current_block.1 = Some(t);
    }

    fn emit_assignment(&mut self, lhs: &SimplePlace, rhs: mlcfg::Exp) {
        let assign = self.create_assign(lhs, rhs);
        self.emit_statement(assign);
    }

    pub fn translate(mut self, nm: DefId, contracts: Contract) -> Function {
        self.translate_body();

        let arg_count = self.body.arg_count;
        let mut vars = self.body.local_decls.iter_enumerated().filter_map(|(loc, decl)| {
            if self.erased_locals.contains(loc) {
                None
            } else {
                let ident = self.translate_local(loc);
                Some((ident, ty::translate_ty(&mut self.ty_ctx, decl.source_info.span, decl.ty)))
            }
        });

        let retty = vars.next().unwrap().1;
        let args = vars.by_ref().take(arg_count).collect();
        let vars = vars.collect::<Vec<_>>();

        let name = translate_value_id(self.tcx, nm);

        move_invariants_into_loop(&mut self.past_blocks);
        Function { name, retty, args, vars, blocks: self.past_blocks, contract: contracts }
    }

    fn translate_body(&mut self) {
        for (bb, bbd) in preorder(self.body) {
            self.current_block = (vec![], None);
            if bbd.is_cleanup {
                continue;
            }
            self.freeze_borrows_at_block_start(bb);

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

    fn freeze_borrows_at_block_start(&mut self, bb: BasicBlock) {
        let pred_blocks = &self.body.predecessors()[bb];

        if pred_blocks.is_empty() {
            return;
        }

        let term_loc = self.body.terminator_loc(pred_blocks[0]);
        self.local_live.seek_before_primary_effect(term_loc);
        let first = self.local_live.get().clone();

        let all_equal = pred_blocks.iter().all(|block| {
            self.local_live.seek_before_primary_effect(self.body.terminator_loc(*block));
            self.local_live.get() == &first
        });

        assert!(all_equal, "predecessors don't all agree on live variables!");
        use ExtendedLocation::*;
        self.freeze_borrows_dying_between(Start(term_loc), Start(bb.start_location()));
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
            let assumption: Exp =
                ty::drop_predicate(&mut self.ty_ctx, local_ty).app_to(ident.into());
            self.emit_statement(mlcfg::Statement::Assume(assumption));
        }
    }

    // Useful helper to translate an operand
    pub fn translate_operand(&mut self, operand: &Operand<'tcx>) -> Exp {
        match operand {
            Operand::Copy(pl) | Operand::Move(pl) => {
                self.translate_rplace(&simplify_place(self.tcx, self.body, pl))
            }
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
    // [(P as Some)]   ---> [_1]
    // [(P as Some).0] ---> let Some(a) = [_1] in a
    // [(* P)] ---> * [P]
    pub fn translate_rplace(&mut self, rhs: &SimplePlace) -> Exp {
        let mut inner = self.translate_local(rhs.local).into();

        for proj in rhs.proj.iter() {
            match proj {
                Deref(Mut) => {
                    inner = Current(box inner);
                }
                Deref(Not) => {
                    // Immutable references are erased in MLCFG
                }
                FieldAccess { base_ty, ctor, ix } => {
                    let def = self.tcx.adt_def(*base_ty);
                    let variant = &def.variants[*ctor];
                    let size = variant.fields.len();

                    let tyname = translate_value_id(self.tcx, variant.def_id);

                    let mut pat = vec![Wildcard; *ix];
                    pat.push(VarP("a".into()));
                    pat.append(&mut vec![Wildcard; size - ix - 1]);

                    inner = Let {
                        pattern: ConsP(tyname, pat),
                        arg: box inner,
                        body: box Var("a".into()),
                    }
                }
                TupleAccess { size, ix } => {
                    let mut pat = vec![Wildcard; *ix];
                    pat.push(VarP("a".into()));
                    pat.append(&mut vec![Wildcard; size - ix - 1]);

                    inner = Let { pattern: TupleP(pat), arg: box inner, body: box Var("a".into()) }
                }
            }
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
    pub fn create_assign(&mut self, lhs: &SimplePlace, rhs: Exp) -> mlcfg::Statement {
        // Translation happens inside to outside, which means we scan projection elements in reverse
        // building up the inner expression. We start with the RHS expression which is at the deepest
        // level.
        let mut inner = rhs;
        // The stump represents the projection up to the element being translated
        let mut stump = lhs.clone();
        for proj in lhs.proj.iter().rev() {
            // Remove the last element from the projection
            stump.proj.pop();

            match proj {
                Deref(M::Mut) => {
                    inner = RecUp {
                        record: box self.translate_rplace(&stump),
                        label: "current".into(),
                        val: box inner,
                    }
                }
                Deref(M::Not) => {
                    // Immutable references are erased in MLCFG
                }
                FieldAccess { ctor, base_ty, ix, .. } => {
                    let def = self.tcx.adt_def(*base_ty);
                    let variant = &def.variants[*ctor];
                    let size = variant.fields.len();
                    let varpats =
                        ('a'..).map(|c| VarP(LocalIdent::Name(c.to_string()))).take(size).collect();

                    let mut varexps: Vec<Exp> =
                        ('a'..).map(|c| Var(c.to_string().into())).take(size).collect();

                    varexps[*ix] = inner;

                    let tyname = translate_value_id(self.tcx, variant.def_id);

                    inner = Let {
                        pattern: ConsP(tyname.clone(), varpats),
                        arg: box self.translate_rplace(&stump),
                        body: box Constructor { ctor: tyname, args: varexps },
                    }
                }
                TupleAccess { size, ix } => {
                    let varpats = ('a'..)
                        .map(|c| VarP(LocalIdent::Name(c.to_string())))
                        .take(*size)
                        .collect();
                    let mut varexps: Vec<_> =
                        ('a'..).map(|c| Var(c.to_string().into())).take(*size).collect();
                    varexps[*ix] = inner;

                    inner = Let {
                        pattern: TupleP(varpats),
                        arg: box self.translate_rplace(&stump),
                        body: box Tuple(varexps),
                    }
                }
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

fn translate_type_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, true)
}

fn translate_value_id(tcx: TyCtxt, def_id: DefId) -> QName {
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
        (_, Some(Namespace::ValueNS)) => {}
        (_, _) => unreachable!(),
    }

    QName { module: mod_segs, name: name_segs }
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

    match c.literal.ty.kind() {
        Int(I8) => {
            Constant::Int(c.literal.val.try_to_bits(Size::from_bytes(1)).unwrap() as i128, Some(ty::i8_ty()))
        }
        Int(I16) => Constant::Int(
            c.literal.val.try_to_bits(Size::from_bytes(2)).unwrap() as i128,
            Some(ty::i16_ty()),
        ),
        Int(I32) => Constant::Int(
            c.literal.val.try_to_bits(Size::from_bytes(4)).unwrap() as i128,
            Some(ty::i32_ty()),
        ),
        Int(I64) => Constant::Int(
            c.literal.val.try_to_bits(Size::from_bytes(8)).unwrap() as i128,
            Some(ty::i64_ty()),
        ),
        Int(I128) => unimplemented!("128-bit integers are not supported"),

        Uint(U8) => {
            Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(1)).unwrap(), Some(ty::u8_ty()))
        }
        Uint(U16) => {
            Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(2)).unwrap(), Some(ty::u16_ty()))
        }
        Uint(U32) => {
            Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(4)).unwrap(), Some(ty::u32_ty()))
        }
        Uint(U64) => {
            Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(8)).unwrap(), Some(ty::u64_ty()))
        }
        Uint(U128) => {
             unimplemented!("128-bit integers are not supported")
        }
        Uint(Usize) => {
            Constant::Uint(c.literal.val.try_to_bits(Size::from_bytes(8)).unwrap(), Some(ty::usize_ty()))
        }
        _ => {
            use rustc_middle::ty::print::{PrettyPrinter, FmtPrinter};
            let mut fmt = String::new();
            let cx = FmtPrinter::new(tcx, &mut fmt, Namespace::ValueNS);
            cx.pretty_print_const(c.literal, false).unwrap();

            Constant::Other(fmt)
        }
    }
}
