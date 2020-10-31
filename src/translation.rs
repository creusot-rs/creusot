use std::collections::HashMap;

use rustc_hir::{def::CtorKind, def_id::DefId};
use rustc_middle::{ty::AdtDef, mir::traversal::preorder, mir::*, mir, ty::TyCtxt};

use crate::{
    analysis::{self, LocationIntervalMap},
    place::from_place,
    place::{MirPlace, Mutability::*, Projection::*},
    polonius::PoloniusInfo,
};

use crate::mlcfg::{MlCfgExp::*, MlCfgPattern::*, *};

use self::ty::TyTranslator;

mod statement;
mod terminator;

mod ty;

pub struct FunctionTranslator<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    pol: PoloniusInfo,
    move_map: LocationIntervalMap<analysis::MoveMap>,
    discr_map: HashMap<(BasicBlock, mir::Local), Place<'tcx>>,

    // Current block being generated
    current_block: (Block, Vec<MlCfgStatement>, Option<MlCfgTerminator>),

    past_blocks: Vec<MlCfgBlock>,
}

pub fn translate_tydecl<'tcx>(tcx: TyCtxt<'tcx>, adt: &AdtDef) -> MlTyDecl {
    TyTranslator::new(tcx).translate_tydecl(adt)
}

impl<'a, 'tcx> FunctionTranslator<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        pol: PoloniusInfo,
        move_map: LocationIntervalMap<analysis::MoveMap>,
        discr_map: HashMap<(BasicBlock, mir::Local), Place<'tcx>>,
    ) -> Self {
        FunctionTranslator {
            tcx,
            body,
            pol,
            move_map,
            discr_map,
            current_block: (BasicBlock::MAX.into(), Vec::new(), None),
            past_blocks: Vec::new(),
        }
    }


    fn emit_statement(&mut self, s: MlCfgStatement) {
        self.current_block.1.push(s);
    }

    fn emit_terminator(&mut self, t: MlCfgTerminator) {
        assert!(self.current_block.2.is_none());

        self.current_block.2 = Some(t);
    }

    pub fn translate(mut self, nm: DefId) -> MlCfgFunction {
        for (bb, bbd) in preorder(self.body) {
            self.current_block = (bb.into(), vec![], None);

            let mut loc = bb.start_location();
            for statement in &bbd.statements {
                self.translate_statement(statement);
                loc = loc.successor_within_block();
            }

            self.translate_terminator(bbd.terminator(), loc);

            self.past_blocks.push(MlCfgBlock{
                label: self.current_block.0,
                statements: self.current_block.1,
                terminator: self.current_block.2.unwrap()
            });
        }

        let ty_trans = TyTranslator::new(self.tcx);
        let mut vars = self.body.local_decls.iter_enumerated().map(|(loc, decl)| {
            (loc, ty_trans.translate_ty(decl.ty) )
        });
        let _retty = vars.nth(0).unwrap();

        let name = self.tcx.def_path(nm).to_filename_friendly_no_crate();
        MlCfgFunction {
            name: name,
            args: vars.by_ref().take(self.body.arg_count).collect(),
            vars: vars.collect::<Vec<_>>(),
            blocks: self.past_blocks,
        }
    }

    // Useful helper to translate an operand
    pub fn translate_operand(&self, operand: &Operand<'tcx>) -> MlCfgExp {
        match operand {
            Operand::Copy(pl)
            | Operand::Move(pl) => rhs_to_why_exp(&from_place(self.tcx, self.body, pl)),
            Operand::Constant(c) => Const(MlCfgConstant::from_mir_constant(self.tcx, c))
,
        }
    }
}


fn translate_defid<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    tcx.def_path_str(def_id).replace("::", ".")
}


// [(P as Some)]   ---> [_1]
// [(P as Some).0] ---> let Some(a) = [_1] in a
// [(* P)] ---> * [P]
pub fn rhs_to_why_exp(rhs: &MirPlace) -> MlCfgExp {
    let mut inner = Local(rhs.local);

    for proj in rhs.proj.iter() {
        match proj {
            Deref(Mut) => {
                inner = Current(box inner);
            }
            Deref(Not) => {
                // Immutable references are erased in MLCFG
            }
            FieldAccess { ctor, ix, size, field, kind } => {
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
    return inner;
}
