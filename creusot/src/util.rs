use crate::ctx::*;
use crate::translation::ty;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{DefIdTree, TyCtxt};
use rustc_span::Symbol;
use why3::{
    declaration::Signature,
    mlcfg::{Constant, Exp},
    Ident,
};

pub fn parent_module(tcx: TyCtxt, def_id: DefId) -> DefId {
    let mut module_id = def_id;

    while let Some(parent) = tcx.parent(module_id) {
        module_id = parent;
        if tcx.def_kind(module_id) == DefKind::Mod {
            break;
        }
    }
    module_id
}

pub fn is_no_translate(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "no_translate"])
        .is_some()
}

pub fn is_contract(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "contract"])
        .is_some()
}

pub fn is_ensures(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "ensures"]).is_some()
}

pub fn is_requires(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "requires"])
        .is_some()
}

pub fn is_variant(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "variant"]).is_some()
}

pub fn is_invariant(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "invariant"])
        .is_some()
}

pub fn is_predicate(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "predicate"])
        .is_some()
}

pub fn is_logic(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "logic"]).is_some()
}

pub fn is_trusted(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::specification::get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "trusted"]).is_some()
}

pub fn should_translate(tcx: TyCtxt, mut def_id: DefId) -> bool {
    loop {
        if is_no_translate(tcx, def_id) {
            return false;
        }

        if tcx.is_closure(def_id) {
            def_id = tcx.parent(def_id).unwrap();
        } else {
            return true;
        }
    }
}

pub(crate) fn method_name(tcx: TyCtxt, def_id: DefId) -> Ident {
    ident_of(tcx.item_name(def_id))
}

pub fn ident_of(id: Symbol) -> Ident {
    Ident::build(&id.as_str().to_lowercase())
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ItemType {
    Logic,
    Predicate,
    Program,
    Trait,
    Impl,
    Type,
    Interface,
}

impl ItemType {
    pub fn clone_interfaces(&self) -> bool {
        use ItemType::*;
        matches!(self, Logic | Predicate | Type | Interface)
    }
}

pub fn item_type(tcx: TyCtxt<'_>, def_id: DefId) -> ItemType {
    match tcx.def_kind(def_id) {
        DefKind::Trait => ItemType::Trait,
        DefKind::Impl => ItemType::Impl,
        DefKind::Fn | DefKind::AssocFn => {
            if is_predicate(tcx, def_id) {
                ItemType::Predicate
            } else if is_logic(tcx, def_id) {
                ItemType::Logic
            } else {
                ItemType::Program
            }
        }
        _ => todo!(),
    }
}

pub fn signature_of<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
) -> Signature {
    let sig = ctx
        .tcx
        .normalize_erasing_late_bound_regions(ctx.tcx.param_env(def_id), ctx.tcx.fn_sig(def_id));

    let pre_contract = crate::specification::contract_of(ctx.tcx, def_id).unwrap();

    let mut contract = pre_contract.check_and_lower(ctx, names, def_id);

    if sig.output().is_never() {
        contract.ensures.push(Exp::Const(Constant::const_false()));
    }

    let arg_names = ctx.tcx.fn_arg_names(def_id);
    let name = translate_value_id(ctx.tcx, def_id);

    Signature {
        // TODO: consider using the function's actual name instead of impl so that trait methods and normal functions have same structure
        name: name.name.into(),
        // TODO: use real span
        retty: Some(ty::translate_ty(ctx, names, rustc_span::DUMMY_SP, sig.output())),
        args: arg_names
            .iter()
            .enumerate()
            .zip(sig.inputs())
            .map(|((ix, id), ty)| {
                let name = if id.name.is_empty() {
                    format!("_{}", ix + 1).into()
                } else {
                    id.name.to_string().into()
                };
                (name, ty::translate_ty(ctx, names, rustc_span::DUMMY_SP, ty))
            })
            .collect(),
        contract,
    }
}

use rustc_ast::{
    token::TokenKind::Literal,
    tokenstream::{TokenStream, TokenTree::*},
};

pub fn ts_to_symbol(ts: TokenStream) -> Option<Symbol> {
    assert_eq!(ts.len(), 1);

    if let Token(tok) = ts.trees().next().unwrap() {
        if let Literal(lit) = tok.kind {
            return Some(lit.symbol);
        }
    }
    None
}
