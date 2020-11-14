use std::collections::HashMap;

use rustc_ast::AttrItem;

use rustc_middle::{
    mir::{BasicBlockData, Place, Rvalue, StatementKind as StmtK, TerminatorKind},
    ty::{Attributes, Ty, TyCtxt, VariantDef},
};

use crate::mlcfg::{Constant, Pattern};

// Find the place being discriminated, if there is one
pub fn discriminator_for_switch<'tcx>(bbd: &BasicBlockData<'tcx>) -> Option<Place<'tcx>> {
    let discr = if let TerminatorKind::SwitchInt { discr, .. } = &bbd.terminator().kind {
        discr
    } else {
        return None;
    };

    if let StmtK::Assign(box (pl, Rvalue::Discriminant(real_discr))) =
        bbd.statements.last().unwrap().kind
    {
        if discr.place() == Some(pl) {
            Some(real_discr)
        } else {
            None
        }
    } else {
        None
    }
}

// Create the patterns for a switch
pub fn branches_for_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    switch_ty: Ty<'tcx>,
    targets: Vec<u128>,
) -> Vec<Pattern> {
    use rustc_middle::ty::TyKind::*;
    match switch_ty.kind() {
        Adt(def, _) => {
            let discr_to_var_idx: HashMap<_, _> =
                def.discriminants(tcx).map(|(idx, d)| (d.val, idx)).collect();

            targets
                .iter()
                .map(|disc| variant_pattern(&def.variants[discr_to_var_idx[&disc]]))
                .collect()
        }
        Tuple(_) => unimplemented!("tuple"),
        Bool => vec![Pattern::LitP(Constant::const_false()), Pattern::LitP(Constant::const_true())],
        _ => unimplemented!("constant pattern"),
    }
}

pub fn variant_pattern(var: &VariantDef) -> Pattern {
    let wilds = var.fields.iter().map(|_| Pattern::Wildcard).collect();
    let cons_name = var.ident.to_string();
    Pattern::ConsP(cons_name, wilds)
}

fn is_attr(attr: &AttrItem, str: &str) -> bool {
    let segments = &attr.path.segments;
    segments.len() >= 2
        && segments[0].ident.as_str() == "creusot"
        && segments[1].ident.as_str() == str
}

pub fn spec_attrs<'tcx>(a: Attributes<'tcx>) -> Vec<&AttrItem> {
    a.iter()
        .filter(|a| !a.is_doc_comment())
        .map(|a| a.get_normal_item())
        .filter(|ai| is_attr(ai, "spec"))
        .collect()
}
