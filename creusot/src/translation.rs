use self::util::spec_attrs;
use crate::mlcfg;
use crate::mlcfg::{Exp::*, Pattern::*, *};
use crate::{mlcfg::Statement::*, place::Mutability as M};
use crate::{
    place::simplify_place,
    place::{Mutability::*, Projection::*, SimplePlace},
};
use rustc_hir::{def::CtorKind, def_id::DefId};
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir::traversal::preorder, mir::*, ty::AdtDef, ty::TyCtxt, ty::TyKind};
use rustc_mir::dataflow::{
    self,
    impls::{MaybeInitializedLocals, MaybeLiveLocals},
    Analysis,
};

pub mod specification;
mod statement;
mod terminator;
mod ty;
pub mod util;

// Split this into several sub-contexts: Core, Analysis, Results?
pub struct FunctionTranslator<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    // pol: PoloniusInfo<'a, 'tcx>,
    local_live: dataflow::ResultsCursor<'a, 'tcx, MaybeLiveLocals>,

    // Whether a local is initialized or not at a location
    local_init: dataflow::ResultsCursor<'a, 'tcx, MaybeInitializedLocals>,

    // Current block being generated
    current_block: (BlockId, Vec<mlcfg::Statement>, Option<mlcfg::Terminator>),

    past_blocks: Vec<mlcfg::Block>,
}

pub fn translate_tydecl(tcx: TyCtxt, adt: &AdtDef) -> MlTyDecl {
    ty::translate_tydecl(tcx, adt)
}

impl<'a, 'tcx> FunctionTranslator<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
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

        FunctionTranslator {
            tcx,
            body,
            local_live,
            local_init,
            current_block: (BasicBlock::MAX.into(), Vec::new(), None),
            past_blocks: Vec::new(),
        }
    }

    fn emit_statement(&mut self, s: mlcfg::Statement) {
        self.current_block.1.push(s);
    }

    fn emit_terminator(&mut self, t: mlcfg::Terminator) {
        assert!(self.current_block.2.is_none());

        self.current_block.2 = Some(t);
    }

    fn emit_assignment(&mut self, lhs: &SimplePlace, rhs: mlcfg::Exp) {
        let assign = self.create_assign(lhs, rhs);
        self.emit_statement(assign);
    }

    pub fn translate(mut self, nm: DefId, contracts: (Vec<String>, Vec<String>)) -> Function {
        for (bb, bbd) in preorder(self.body) {
            self.current_block = (bb.into(), vec![], None);
            if bbd.is_cleanup {
                continue;
            }

            let mut loc = bb.start_location();
            for statement in &bbd.statements {
                self.freeze_borrows_dying_at(loc);
                self.translate_statement(statement);
                loc = loc.successor_within_block();
            }

            self.freeze_borrows_dying_at(loc);
            self.translate_terminator(bbd.terminator(), loc);

            self.past_blocks.push(Block {
                label: self.current_block.0,
                statements: self.current_block.1,
                terminator: self.current_block.2.unwrap(),
            });
        }

        self.current_block = (BasicBlock::MAX.into(), Vec::new(), None);

        let mut vars = self.body.local_decls.iter_enumerated().filter_map(|(loc, decl)| {
            if self.artifact_decl(decl) {
                None
            } else {
                let ident = self.translate_local(loc);
                Some((ident, ty::translate_ty(self.tcx, decl.ty)))
            }
        });
        let retty = vars.next().unwrap().1;

        let name = self.tcx.def_path(nm).to_filename_friendly_no_crate();
        Function {
            name,
            retty,
            args: vars.by_ref().take(self.body.arg_count).collect(),
            vars: vars.collect::<Vec<_>>(),
            blocks: self.past_blocks,
            preconds: contracts.0,
            postconds: contracts.1,
        }
    }

    fn freeze_borrows_dying_at(&mut self, loc: Location) {
        let body2 = self.body;
        let predecessors = if loc.statement_index == 0 {
            self.body.predecessors()[loc.block].iter().map(|bb| body2.terminator_loc(*bb)).collect()
        } else {
            let mut pred = loc;
            pred.statement_index -= 1;
            vec![pred]
        };

        let mut previous_locals: Vec<BitSet<_>> = predecessors
            .iter()
            .map(|pred| {
                self.local_live.seek_after_primary_effect(*pred);
                self.local_live.get().clone()
            })
            .collect();
        previous_locals.dedup();
        if previous_locals.is_empty() {
            return;
        }

        assert!(
            previous_locals.len() <= 1,
            "all predecessors must agree on liveness {:?}",
            previous_locals
        );

        let mut dying_locals = previous_locals.remove(0);

        self.local_live.seek_after_primary_effect(loc);

        dying_locals.subtract(self.local_live.get());
        for local in dying_locals.iter() {
            self.local_init.seek_before_primary_effect(loc);
            // Freeze all dying variables that were initialized and are mutable references
            let local_ty = self.body.local_decls[local].ty;

            if self.local_init.contains(local) && local_ty.is_ref() && local_ty.is_mutable_ptr() {
                let ident = self.translate_local(local);
                self.emit_statement(mlcfg::Statement::Freeze(ident));
            }
        }
    }

    // Useful helper to translate an operand
    pub fn translate_operand(&self, operand: &Operand<'tcx>) -> Exp {
        match operand {
            Operand::Copy(pl) | Operand::Move(pl) => {
                self.translate_rplace(&simplify_place(self.tcx, self.body, pl))
            }
            Operand::Constant(c) => Const(mlcfg::Constant::from_mir_constant(self.tcx, c)),
        }
    }

    /// Checks whether a local declaration is actuall related to specifications
    /// and should be excluded entirely from the outputted MLCFG
    fn artifact_decl(&self, decl: &LocalDecl) -> bool {
        if let TyKind::Closure(def_id, _) = decl.ty.peel_refs().kind() {
            if !spec_attrs(self.tcx.get_attrs(*def_id)).is_empty() {
                return true;
            }
        }
        false
    }

    fn translate_local(&self, loc: Local) -> LocalIdent {
        let debug_info : Vec<_> = self.body.var_debug_info.iter().filter(|var_info| {
            match var_info.place.as_local(){
                Some(l) => l == loc,
                None => false
            }
        }).collect();

        assert!(debug_info.len() <= 1, "expected at most one debug entry for local {:?}", loc);

        match debug_info.get(0) {
            Some(info) => {
                LocalIdent::Local(loc, Some(info.name.to_string()))
            }
            None => loc.into(),
        }

    }
    // [(P as Some)]   ---> [_1]
    // [(P as Some).0] ---> let Some(a) = [_1] in a
    // [(* P)] ---> * [P]
    pub fn translate_rplace(&self, rhs: &SimplePlace) -> Exp {
        let mut inner = self.translate_local(rhs.local).into();

        for proj in rhs.proj.iter() {
            match proj {
                Deref(Mut) => {
                    inner = Current(box inner);
                }
                Deref(Not) => {
                    // Immutable references are erased in MLCFG
                }
                FieldAccess { ctor, ix, size, field: _, kind } => {
                    match kind {
                        // Tuple
                        CtorKind::Fn | CtorKind::Fictive => {
                            let mut pat = vec![Wildcard; *ix];
                            pat.push(VarP("a".into()));
                            pat.append(&mut vec![Wildcard; size - ix - 1]);

                            inner = Let {
                                pattern: ConsP(ctor.to_string(), pat),
                                arg: box inner,
                                body: box Var("a".into()),
                            }
                        }
                        // Unit
                        CtorKind::Const => {
                            assert!(*size == 1 && *ix == 0);
                            unimplemented!();
                        }
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
    pub fn create_assign(
        &self,
        lhs: &SimplePlace,
        rhs: Exp,
    ) -> mlcfg::Statement {
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
                FieldAccess { ctor, ix, size, kind, .. } => match kind {
                    CtorKind::Fn | CtorKind::Fictive => {
                        let varpats = ('a'..).map(|c| VarP(LocalIdent::Name(c.to_string()))).take(*size).collect();
                        let mut varexps: Vec<Exp> =
                            ('a'..).map(|c| Var(c.to_string().into())).take(*size).collect();
                        varexps[*ix] = inner;

                        inner = Let {
                            pattern: ConsP(ctor.to_string(), varpats),
                            arg: box self.translate_rplace(&stump),
                            body: box Constructor { ctor: ctor.into(), args: varexps },
                        }
                    }
                    CtorKind::Const => inner = Constructor { ctor: ctor.into(), args: vec![] },
                },
                TupleAccess { size, ix } => {
                    let varpats = ('a'..).map(|c| VarP(LocalIdent::Name(c.to_string()))).take(*size).collect();
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

fn translate_defid(tcx: TyCtxt, def_id: DefId) -> QName {
    QName { segments: tcx.def_path_str(def_id).split("::").map(|s| s.to_string()).collect() }
}
