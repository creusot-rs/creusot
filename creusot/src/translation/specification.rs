use std::collections::HashMap;

use itertools::Itertools;
use rustc_ast::{
    token::TokenKind::Literal, tokenstream::TokenStream, tokenstream::TokenTree::Token, Attribute,
};
use rustc_hir::{def_id::DefId, definitions::DefPathData};
use rustc_middle::{
    mir::{
        traversal::postorder, BasicBlock, BasicBlockData, Body, MirPhase, Operand, Rvalue,
        StatementKind as StmtK, TerminatorKind, START_BLOCK,
    },
    ty::{Attributes, TyCtxt},
};
use rustc_mir::transform::*;

use crate::{
    is_attr,
    mlcfg::{MlCfgConstant, MlCfgExp, MlCfgPattern, MlCfgPred, MlCfgPredFunction},
    place::from_place,
};

use super::{operand_to_exp, rhs_to_why_exp};

use crate::translation::util::*;

pub struct SpecificationTranslator<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub body: Body<'tcx>,
    pub attrs: Attributes<'tcx>,
    pub def_id: DefId,
}
// Translate a specification to a whycfg expression.
// Currently specifications are lambda-lifted to the top level, recursively.
// This current version of the translator will just translate those specifications
// directly into why3 rather than trying to reconstitute a single expression.
// At a later date I may need to figure out how to collect the bodies of specs that
// are related to gether and glue them together.
//
// 1. Use some sort of identifiers to identify groups of specification bodies:
//  a. How do we know which body corresponds to the top level spec?
// 2. Harvest _all_ specification bodies in the source, and do a recursive translation,
// each closure call then becomes a recursive translation of the appropriate body.
impl<'tcx> SpecificationTranslator<'tcx> {
    pub fn translate(&mut self) -> MlCfgPredFunction {
        assert!(!self.body.is_cfg_cyclic(), "specification must be acyclic");

        run_passes(
            self.tcx,
            &mut self.body,
            MirPhase::Optimization,
            &[&[
                // Remove unwind
                &no_landing_pads::NoLandingPads::new(self.tcx),
                // Remove falsedge
                &simplify_branches::SimplifyBranches::new("initial"),
                // Remove FakeRead etc
                &cleanup_post_borrowck::CleanupNonCodegenStatements,
                // COmpact the CFG
                &simplify::SimplifyCfg::new("initial"),
            ]],
        );

        // Because there are no anonymous recursive functions or loops in
        // our term language, the terminators should always be switches
        // or jumps to the return block. Let's verify that.

        // Find ther return block.
        let term_block = self
            .body
            .basic_blocks()
            .iter_enumerated()
            .filter(|(_bb, bbd)| matches!(bbd.terminator().kind, TerminatorKind::Return { .. }))
            .next()
            .expect("expected at least one return block")
            .0;

        let correct_structure = self.body.basic_blocks().iter_enumerated().all(|(bb, bbd)| {
            match bbd.terminator().kind {
                TerminatorKind::SwitchInt { .. } => true,
                TerminatorKind::Goto { target } => target == term_block,
                // ensure there is a single return block. not a critical restriction
                TerminatorKind::Return { .. } => term_block == bb,
                _ => {
                    dbg!(bbd);
                    false
                }
            }
        });

        assert!(correct_structure);

        let mut blocks = HashMap::new();
        for (bb, bbd) in postorder(&self.body) {
            let mut inner = self.translate_terminator(&mut blocks, bbd);

            let mut stmt_iter = bbd.statements.iter().rev();
            while let Some(stmt) = stmt_iter.next() {
                match &stmt.kind {
                    StmtK::Assign(box (pl, rval)) => {
                        let var = pl.as_local().unwrap();

                        let outer = match rval {
                            Rvalue::Use(rval) => match rval {
                                Operand::Move(pl) | Operand::Copy(pl) => MlCfgPred::Exp(
                                    rhs_to_why_exp(&from_place(self.tcx, &self.body, pl)),
                                ),
                                Operand::Constant(box c) => MlCfgPred::Exp(MlCfgExp::Const(
                                    MlCfgConstant::from_mir_constant(self.tcx, c),
                                )),
                            },
                            Rvalue::BinaryOp(op, l, r) | Rvalue::CheckedBinaryOp(op, l, r) => {
                                MlCfgPred::Exp(MlCfgExp::BinaryOp(*op, box operand_to_exp(self.tcx, &self.body, l), box operand_to_exp(self.tcx, &self.body, r)))
                            }
                            Rvalue::UnaryOp(_, _) => unimplemented!(),
                            Rvalue::Discriminant(pl) => MlCfgPred::Exp(rhs_to_why_exp(
                                &from_place(self.tcx, &self.body, &pl),
                            )),
                            // Rvalue::Aggregate(_, _) => {}
                            _ => {
                                panic!("unsupported rvalue in spec");
                            }
                        };

                        inner = MlCfgPred::Let(var, box outer, box inner);
                    }
                    StmtK::FakeRead(_, _) | StmtK::StorageLive(_) | StmtK::StorageDead(_) => {}
                    _ => panic!("unexpected statement kind"),
                }
            }

            blocks.insert(bb, inner);
        }

        MlCfgPredFunction {
            name: "pred_name".to_owned(),
            body: blocks.remove(&START_BLOCK).unwrap(),
            args: vec![],
        }
    }

    fn translate_terminator(
        &self,
        succs: &mut HashMap<BasicBlock, MlCfgPred>,
        bbd: &BasicBlockData<'tcx>,
    ) -> MlCfgPred {
        match &bbd.terminator().kind {
            TerminatorKind::Goto { target } => succs[&target].clone(),
            TerminatorKind::SwitchInt { discr, switch_ty: _, targets } => {
                let real_discr = discriminator_for_switch(bbd);
                let discriminator_exp = real_discr
                    .or_else(|| discr.place())
                    .map(|pl| rhs_to_why_exp(&from_place(self.tcx, &self.body, &pl)))
                    .unwrap_or_else(|| {
                        MlCfgExp::Const(MlCfgConstant::from_mir_constant(
                            self.tcx,
                            discr.constant().unwrap(),
                        ))
                    });

                let discr_ty =
                    real_discr.map(Operand::Move).unwrap_or(discr.clone()).ty(&self.body, self.tcx);

                let patterns =
                    branches_for_ty(self.tcx, discr_ty, targets.iter().map(|i| i.0).collect());

                let mut branches: Vec<_> = targets
                    .iter()
                    .zip(patterns.iter())
                    .map(|((_, t), p)| (p.clone(), succs[&t].clone()))
                    .collect();

                branches.push((MlCfgPattern::Wildcard, succs[&targets.otherwise()].clone()));

                MlCfgPred::Switch(box MlCfgPred::Exp(discriminator_exp), branches)
            }
            TerminatorKind::Return => MlCfgPred::Exp(MlCfgExp::Var("_0".to_owned())),
            _ => unreachable!("invalid terminator for specification function {:?}", &bbd),
        }
    }

    fn rebuild_predicate(&self, mut subexps: Vec<MlCfgExp>) -> MlCfgPred {
        let spec_attr = spec_kind_attr(self.attrs).expect("no spec attribute");

        match ts_to_symbol(spec_attr.get_normal_item().args.inner_tokens()).as_ref() {
            "conj" => MlCfgPred::Conj(
                box MlCfgPred::Exp(subexps.remove(0)),
                box MlCfgPred::Exp(subexps.remove(0)),
            ),
            "expr" => MlCfgPred::Exp(subexps.remove(0)),
            "impl" => MlCfgPred::Impl(
                box MlCfgPred::Exp(subexps.remove(0)),
                box MlCfgPred::Exp(subexps.remove(0)),
            ),
            "disj" => MlCfgPred::Disj(
                box MlCfgPred::Exp(subexps.remove(0)),
                box MlCfgPred::Exp(subexps.remove(0)),
            ),

            a => panic!("oh no: {}", a),
        }
    }
}

fn spec_kind_attr<'tcx>(attrs: Attributes<'tcx>) -> Option<Attribute> {
    attrs
        .iter()
        .filter(|attr| !attr.is_doc_comment() && is_attr(attr.get_normal_item(), "spec"))
        .cloned()
        .collect::<Vec<_>>()
        .iter()
        .cloned()
        .next()
}

fn ts_to_symbol(ts: TokenStream) -> String {
    assert_eq!(ts.len(), 1);

    if let Token(tok) = ts.trees().next().unwrap() {
        if let Literal(lit) = tok.kind {
            return lit.symbol.to_string();
        }
    }
    panic!("not a single token")
}

fn closure_name(tcx: TyCtxt, def_id: DefId) -> String {
    let def_path = tcx.def_path(def_id);
    format!(
        "{}",
        def_path.data.iter().format_with("_", |elt, f| match elt.data {
            DefPathData::ClosureExpr => f(&format_args!("{}", elt.disambiguator)),
            _ => f(&format_args!("{}", elt.data)),
        })
    )
}
