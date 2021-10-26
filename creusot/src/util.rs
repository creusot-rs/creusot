use crate::ctx::*;
use crate::translation::ty;
use rustc_ast::{AttrItem, AttrKind, Attribute};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::Attributes;
use rustc_middle::ty::{DefIdTree, TyCtxt};
use rustc_span::Symbol;
use why3::QName;
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

pub(crate) fn is_no_translate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs(def_id), &["creusot", "no_translate"]).is_some()
}

pub(crate) fn is_spec(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs(def_id), &["creusot", "decl", "spec"]).is_some()
}

pub(crate) fn invariant_name(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "invariant"])
        .and_then(|a| ts_to_symbol(a.args.inner_tokens()))
}

pub(crate) fn is_invariant(tcx: TyCtxt, def_id: DefId) -> bool {
    invariant_name(tcx, def_id).is_some()
}

pub(crate) fn is_assertion(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs(def_id), &["creusot", "spec", "assert"]).is_some()
}

pub(crate) fn is_predicate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs(def_id), &["creusot", "decl", "predicate"]).is_some()
}

pub(crate) fn is_logic(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs(def_id), &["creusot", "decl", "logic"]).is_some()
}

pub(crate) fn is_trusted(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs(def_id), &["creusot", "decl", "trusted"]).is_some()
}

pub(crate) fn is_pure(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs(def_id), &["creusot", "decl", "pure"]).is_some()
}

pub(crate) fn should_translate(tcx: TyCtxt, mut def_id: DefId) -> bool {
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

pub(crate) fn has_body(ctx: &mut TranslationCtx, def_id: DefId) -> bool {
    if let Some(local_id) = def_id.as_local() {
        let hir_id = ctx.tcx.hir().local_def_id_to_hir_id(local_id);
        ctx.tcx.hir().maybe_body_owned_by(hir_id).is_some()
    } else {
        match item_type(ctx.tcx, def_id) {
            ItemType::Logic | ItemType::Predicate | ItemType::Pure => ctx.term(def_id).is_some(),
            _ => false,
        }
    }
}

pub fn get_builtin(tcx: TyCtxt, def_id: DefId) -> Option<QName> {
    get_attr(tcx.get_attrs(def_id), &["creusot", "builtins"])
        .and_then(|a| ts_to_symbol(a.args.inner_tokens()))
        .and_then(|a| QName::from_string(&a.as_str()))
}

pub(crate) fn method_name(tcx: TyCtxt, def_id: DefId) -> Ident {
    ident_of(tcx.item_name(def_id))
}

pub fn ident_of(id: Symbol) -> Ident {
    Ident::build(&id.as_str().to_lowercase())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemType {
    Logic,
    Predicate,
    Program,
    Trait,
    Impl,
    Type,
    AssocTy,
    Interface,
    Pure,
}

impl ItemType {
    // Whether this definition should be 'transparent' which affects
    // how we clone it. Transparent definitions will clone the *interface*
    // of their dependencies, even in their body module. In particular
    // this is used to get around the generativity of why3 clones for logic
    // functions.
    pub fn is_transparent(&self) -> bool {
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
            } else if is_pure(tcx, def_id) {
                ItemType::Pure
            } else {
                ItemType::Program
            }
        }
        DefKind::Struct | DefKind::Enum => ItemType::Type,
        DefKind::AssocTy => ItemType::AssocTy,
        dk => todo!("{:?}", dk),
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

    let mut contract = names.with_public_clones(|names| {
        let pre_contract = crate::specification::contract_of(ctx, def_id).unwrap();
        pre_contract.check_and_lower(ctx, names, def_id)
    });

    if sig.output().is_never() {
        contract.ensures.push(Exp::Const(Constant::const_false()));
    }

    let name = translate_value_id(ctx.tcx, def_id);

    let span = ctx.tcx.def_span(def_id);
    let args = names.with_public_clones(|names| {
        let arg_names = ctx.tcx.fn_arg_names(def_id);
        arg_names
            .iter()
            .enumerate()
            .map(|(ix, id)| {
                if id.name.is_empty() {
                    format!("_{}", ix + 1).into()
                } else {
                    id.name.to_string().into()
                }
            })
            .zip(sig.inputs().iter().map(|ty| ty::translate_ty(ctx, names, span, ty)))
            .collect()
    });

    Signature {
        // TODO: consider using the function's actual name instead of impl so that trait methods and normal functions have same structure
        name: name.name,
        // TODO: use real span
        retty: Some(
            names.with_public_clones(|names| ty::translate_ty(ctx, names, span, sig.output())),
        ),
        args,
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

pub fn is_attr(attr: &Attribute, str: &str) -> bool {
    match attr.kind {
        AttrKind::DocComment(..) => false,
        AttrKind::Normal(ref i, _) => {
            let segments = &i.path.segments;
            segments.len() >= 2
                && segments[0].ident.as_str() == "creusot"
                && segments[1].ident.as_str() == str
        }
    }
}
