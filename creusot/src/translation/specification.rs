use std::collections::HashMap;

use crate::translation::specification;
use crate::{ctx::*, util};
use rustc_middle::ty::Attributes;
use why3::declaration::Contract;
use why3::mlcfg::Exp;

use super::LocalIdent;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Body, ty::TyCtxt};

mod lower;
pub mod typing;

pub use lower::*;

pub fn requires_to_why<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    req_id: DefId,
) -> Exp {
    log::debug!("require clause {:?}", req_id);
    let term = specification::typing::typecheck(ctx.tcx, req_id.expect_local());
    lower_term_to_why3(ctx, names, req_id, term)
}

pub fn variant_to_why<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    var_id: DefId,
) -> Exp {
    log::debug!("variant clause {:?}", var_id);
    let term = specification::typing::typecheck(ctx.tcx, var_id.expect_local());
    lower_term_to_why3(ctx, names, var_id, term)
}

pub fn ensures_to_why<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    ens_id: DefId,
) -> Exp {
    log::debug!("ensures clause {:?}", ens_id);
    let term = specification::typing::typecheck(ctx.tcx, ens_id.expect_local());
    lower_term_to_why3(ctx, names, ens_id, term)
}

pub struct PreContract {
    pub variant: Option<DefId>,
    pub requires: Vec<DefId>,
    pub ensures: Vec<DefId>,
}

impl PreContract {
    fn new() -> Self {
        Self { variant: None, requires: Vec::new(), ensures: Vec::new() }
    }

    pub fn check_and_lower<'tcx>(
        self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        _: DefId,
    ) -> Contract {
        let mut out = Contract::new();

        for req in self.requires {
            out.requires.push(requires_to_why(ctx, names, req));
        }

        for ens in self.ensures {
            out.ensures.push(ensures_to_why(ctx, names, ens));
        }

        if let Some(variant) = self.variant {
            out.variant = vec![variant_to_why(ctx, names, variant)];
        };
        out
    }
}

// Turn a typing context into a substition.
pub fn inv_subst(body: &Body) -> HashMap<why3::Ident, Exp> {
    use rustc_middle::mir::VarDebugInfoContents::Place;

    body.var_debug_info
        .iter()
        .map(|vdi| {
            let loc = match vdi.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!(),
            };
            let source_name = vdi.name.to_string();
            (source_name.into(), Exp::Var(LocalIdent::dbg(loc, vdi).ident()))
        })
        .collect()
}

#[derive(Debug)]
pub enum SpecAttrError {
    InvalidTokens,
}

pub fn contract_of(tcx: TyCtxt, def_id: DefId) -> Result<PreContract, SpecAttrError> {
    let attrs = tcx.get_attrs(def_id);

    use SpecAttrError::*;
    let mut contract = PreContract::new();

    for attr in attrs {
        if attr.is_doc_comment() {
            continue;
        }

        let attr = attr.get_normal_item();

        if !is_attr(attr, "spec") {
            continue;
        }

        match attr.path.segments[2].ident.to_string().as_str() {
            "requires" => {
                let req_name = util::ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?;
                let req_id = tcx.get_diagnostic_item(req_name).ok_or(InvalidTokens)?;
                contract.requires.push(req_id);
            }
            "ensures" => {
                let ens_name = util::ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?;
                let ens_id = tcx.get_diagnostic_item(ens_name).ok_or(InvalidTokens)?;
                contract.ensures.push(ens_id);
            }
            "variant" => {
                let var_name = util::ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?;
                let var_id = tcx.get_diagnostic_item(var_name).ok_or(InvalidTokens)?;
                contract.variant = Some(var_id);
            }
            _ => {}
        }
    }

    Ok(contract)
}

pub fn get_attr<'a>(attrs: Attributes<'a>, path: &[&str]) -> Option<&'a AttrItem> {
    for attr in attrs.iter() {
        if attr.is_doc_comment() {
            continue;
        }

        let attr = attr.get_normal_item();

        let matches = attr
            .path
            .segments
            .iter()
            .zip(path.iter())
            .fold(true, |acc, (seg, s)| acc && &*seg.ident.as_str() == *s);

        if matches {
            return Some(attr);
        }
    }
    None
}

use rustc_ast::AttrItem;

fn is_attr(attr: &AttrItem, str: &str) -> bool {
    let segments = &attr.path.segments;
    segments.len() >= 2
        && segments[0].ident.as_str() == "creusot"
        && segments[1].ident.as_str() == str
}
