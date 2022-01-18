use std::collections::HashMap;

use crate::translation::function::real_locals;
use crate::{ctx::*, util};
use rustc_macros::{TyDecodable, TyEncodable};
use why3::declaration::Contract;
use why3::mlcfg::Exp;

use super::LocalIdent;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Location};
use rustc_middle::ty::TyCtxt;

mod builtins;
mod lower;
pub mod typing;

pub use lower::*;

pub fn requires_to_why<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    req_id: DefId,
) -> Exp {
    log::debug!("require clause {:?}", req_id);
    let term = ctx.term(req_id).unwrap().clone();
    lower_pure(ctx, names, req_id, term)
}

pub fn variant_to_why<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    var_id: DefId,
) -> Exp {
    log::debug!("variant clause {:?}", var_id);
    let term = ctx.term(var_id).unwrap().clone();
    lower_pure(ctx, names, var_id, term)
}

pub fn ensures_to_why<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    ens_id: DefId,
) -> Exp {
    log::debug!("ensures clause {:?}", ens_id);
    let term = ctx.term(ens_id).unwrap().clone();
    lower_pure(ctx, names, ens_id, term)
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
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
pub fn inv_subst(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, loc: Location) -> HashMap<why3::Ident, Exp> {
    use rustc_middle::mir::VarDebugInfoContents::Place;
    let local_map = real_locals(tcx, body);
    let mut scope = body.source_info(loc).scope;

    let mut args = HashMap::new();
    loop {
        for var_info in &body.var_debug_info {
            if var_info.source_info.scope != scope {
                continue;
            }

            let loc = match var_info.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!(),
            };
            let loc = local_map[&loc];
            let source_name = var_info.name.to_string();
            args.entry(source_name.into())
                .or_insert_with(|| Exp::pure_var(LocalIdent::dbg(loc, var_info).ident()));
        }

        if let Some(parent) = body.source_scopes[scope].parent_scope {
            scope = parent
        } else {
            break;
        }
    }

    return args;
}

#[derive(Debug)]
pub enum SpecAttrError {
    InvalidTokens,
}

pub fn contract_of(ctx: &TranslationCtx, def_id: DefId) -> Result<PreContract, SpecAttrError> {
    let attrs = ctx.tcx.get_attrs(def_id);

    use SpecAttrError::*;
    let mut contract = PreContract::new();

    if let Some(extern_spec) = ctx.extern_spec(def_id) {
        return Ok(extern_spec.contract.clone());
    }

    for attr in attrs {
        if !util::is_attr(attr, "spec") {
            continue;
        }

        let attr = attr.get_normal_item();

        // Stop using diagnostic item.
        // Use a custom HIR visitor which walks the attributes
        match attr.path.segments[2].ident.to_string().as_str() {
            "requires" => {
                let req_name = util::ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?;
                let req_id = ctx.creusot_item(req_name).ok_or(InvalidTokens)?;
                contract.requires.push(req_id);
            }
            "ensures" => {
                let ens_name = util::ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?;
                let ens_id = ctx.creusot_item(ens_name).ok_or(InvalidTokens)?;
                contract.ensures.push(ens_id);
            }
            "variant" => {
                let var_name = util::ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?;
                let var_id = ctx.creusot_item(var_name).ok_or(InvalidTokens)?;
                contract.variant = Some(var_id);
            }
            _ => {}
        }
    }

    Ok(contract)
}
