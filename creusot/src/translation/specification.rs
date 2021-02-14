use std::collections::HashMap;

use crate::mlcfg::printer::FormatEnv;
use crate::mlcfg::LocalIdent;
use crate::mlcfg::{self, Exp};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, SourceInfo},
    ty::TyCtxt,
};
use syn::term::*;

use pearlite::term;
mod context;
mod lower;

pub use context::*;
use lower::*;

pub fn requires_to_why<'tcx>(
    res: &RustcResolver<'tcx>,
    body: &Body<'tcx>,
    attr_val: String,
) -> Exp {
    let p: Term = syn::parse_str(&attr_val).unwrap();
    let entry_ctx = context_at_entry(res.2, body);
    let mut tyctx =
        pearlite::typing::TypeContext::new_with_ctx(RustcContext(res.2), entry_ctx);
    let mut t = term::Term::from_syn(res, p).unwrap();

    pearlite::typing::check_term(&mut tyctx, &mut t, &term::Type::BOOLEAN).unwrap();
    // TODO: perform substitution on pearlite?
    lower_term_to_why(res.2, t)
}

pub fn variant_to_why<'tcx>(res: &RustcResolver<'tcx>, body: &Body<'tcx>, attr_val: String) -> Exp {
    let p: Term = syn::parse_str(&attr_val).unwrap();
    let entry_ctx = context_at_entry(res.2, body);
    let mut tyctx =
        pearlite::typing::TypeContext::new_with_ctx(RustcContext(res.2), entry_ctx);
    let mut t = term::Term::from_syn(res, p).unwrap();

    pearlite::typing::infer_term(&mut tyctx, &mut t).unwrap();
    // TODO: perform substitution on pearlite?
    lower_term_to_why(res.2, t)
}

pub fn ensures_to_why<'tcx>(res: &RustcResolver<'tcx>, body: &Body<'tcx>, attr_val: String) -> Exp {
    let p: Term = syn::parse_str(&attr_val).unwrap();
    let mut ctx = context_at_entry(res.2, body);
    let ret_ty = return_ty(res.2, body);
    ctx.push(("result".into(), ret_ty));

    let mut tyctx = pearlite::typing::TypeContext::new_with_ctx(RustcContext(res.2), ctx);

    let mut t = term::Term::from_syn(res, p).unwrap();

    pearlite::typing::check_term(&mut tyctx, &mut t, &term::Type::BOOLEAN).unwrap();
    // TODO: perform substitution on pearlite?
    lower_term_to_why(res.2, t)
}

pub fn invariant_to_why<'tcx>(
    res: &RustcResolver<'tcx>,
    body: &Body<'tcx>,
    info: SourceInfo,
    attr_val: String,
) -> String {
    let p: Term = syn::parse_str(&attr_val).unwrap();
    let ctx: Vec<_> = body
        .var_debug_info
        .iter()
        .filter(|vdi| vdi.source_info.scope <= info.scope)
        .map(|vdi| {
            let info_loc = match vdi.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!("unexpected constant in body arguments"),
            };

            let decl = &body.local_decls[info_loc];

            (vdi.name.to_string(), ty_to_pearlite(res.2, decl.ty))
        })
        .collect();
    let mut tyctx = pearlite::typing::TypeContext::new_with_ctx(RustcContext(res.2), ctx);

    let mut t = term::Term::from_syn(res, p).unwrap();
    pearlite::typing::check_term(&mut tyctx, &mut t, &term::Type::BOOLEAN).unwrap();
    let mut e = lower_term_to_why(res.2, t);
    let fvs = e.fvs();

    let vars_in_scope: Vec<_> =
        body.var_debug_info.iter().filter(|vdi| vdi.source_info.scope <= info.scope).collect();

    use rustc_middle::mir::VarDebugInfoContents::Place;

    // TODO: ensure only one match
    let subst: HashMap<_, _> = fvs
        .iter()
        .map(|free| {
            let var_info = vars_in_scope
                .iter()
                .find(|vdi| free.to_string() == vdi.name.to_ident_string())
                .unwrap();

            let loc = match var_info.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!(),
            };
            (free.clone(), LocalIdent::Local(loc, Some(var_info.name.to_string())).into())
        })
        .collect();
        //
    e.subst(&subst);
    format!("{}", FormatEnv { scope: &[], indent: 0 }.to(&e))
}

// Translate a logical funciton into why.
pub fn logic_to_why<'tcx>(
    res: &RustcResolver<'tcx>,
    did: DefId,
    body: &Body<'tcx>,
    exp: String,
) -> crate::mlcfg::Logic {
    // Technically we should pass through translation::ty here in case we mention
    // any untranslated types...
    let ret_ty = return_ty(res.2, body);
    let entry_ctx = context_at_entry(res.2, body);
    let mut tyctx =
        pearlite::typing::TypeContext::new_with_ctx(RustcContext(res.2), entry_ctx.clone());
    let p: Term = syn::parse_str(&exp).unwrap();

    let mut t = term::Term::from_syn(res, p).unwrap();

    pearlite::typing::check_term(&mut tyctx, &mut t, &ret_ty).unwrap();
    let body = lower_term_to_why(res.2, t);

    let name = crate::translation::translate_defid(res.2, did, rustc_resolve::Namespace::ValueNS);
    mlcfg::Logic {
        name,
        retty: lower_type_to_why(ret_ty),
        args: entry_ctx
            .into_iter()
            .map(|(nm, ty)| (LocalIdent::Name(nm), lower_type_to_why(ty)))
            .collect(),
        body,
        contract: mlcfg::Contract::new(),
    }
}

fn return_ty<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> pearlite::term::Type {
    let ret = &body.local_decls[0u32.into()];

    ty_to_pearlite(tcx, ret.ty)
}

// Constructs a typing environment which contains entries for all arguments of a mir body.
fn context_at_entry<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<(String, pearlite::term::Type)> {
    // CORRECTNESS: Assumes that local_decls and var_debug_info are
    // ordered the same way and have the same elements (at least for arg_count entries).
    // This seems reasonable, since we should have debug info for all function arguments
    let arg_decl = body.local_decls.iter_enumerated().skip(1).take(body.arg_count);
    let arg_info = body.var_debug_info.iter().take(body.arg_count);

    let mut ctx = Vec::new();
    for ((loc, decl), info) in arg_decl.zip(arg_info) {
        use rustc_middle::mir::VarDebugInfoContents::Place;
        let info_loc = match info.value {
            Place(p) => p.as_local().unwrap(),
            _ => panic!("unexpected constant in body arguments"),
        };
        assert_eq!(loc, info_loc, "body local declarations are different from debug info");

        let name = info.name.to_string();
        let ty = ty_to_pearlite(tcx, decl.ty);

        ctx.push((name, ty));
    }

    ctx
}

// Turn a typing context into a substition.
pub fn subst_for_arguments(body: &Body) -> HashMap<LocalIdent, Exp> {
    use rustc_middle::mir::VarDebugInfoContents::Place;

    body.var_debug_info
        .iter()
        .take(body.arg_count)
        .map(|vdi| {
            let loc = match vdi.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!(),
            };
            let source_name = vdi.name.to_string();
            let outer_name = format!("o_{}", source_name);
            (LocalIdent::Name(source_name), Exp::Var(LocalIdent::Local(loc, Some(outer_name))))
        })
        .collect()
}

use rustc_ast::{
    token::TokenKind::Literal,
    tokenstream::{TokenStream, TokenTree::*},
};
use rustc_middle::ty::Attributes;

fn ts_to_symbol(ts: TokenStream) -> Option<String> {
    assert_eq!(ts.len(), 1);

    if let Token(tok) = ts.trees().next().unwrap() {
        if let Literal(lit) = tok.kind {
            return unescape::unescape(&lit.symbol.as_str());
        }
    }
    None
}

fn invariant_name(attr: &rustc_ast::AttrItem) -> String {
    attr.path.segments[3].ident.name.to_string()
}

// TODO: Stop putting strings!!
pub struct Contract {
    pub variant: Option<String>,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
}

impl Contract {
    fn new() -> Self {
        Self { variant: None, requires: Vec::new(), ensures: Vec::new() }
    }

    fn is_empty(&self) -> bool {
        self.variant.is_none() && self.requires.is_empty() && self.ensures.is_empty()
    }

    pub fn check_and_lower<'tcx>(
        self,
        res: &RustcResolver<'tcx>,
        body: &Body<'tcx>,
    ) -> mlcfg::Contract {
        let mut out = mlcfg::Contract::new();

        for req in self.requires {
            out.requires.push(requires_to_why(res, body, req));
        }

        for ens in self.ensures {
            out.ensures.push(ensures_to_why(res, body, ens));
        }

        if let Some(variant) = self.variant {
            out.variant = Some(variant_to_why(res, body, variant));
        };
        out
    }
}

#[derive(Debug)]
pub enum SpecAttrError {
    UnknownAttribute(String),
    InvalidTokens,
}

pub enum Spec {
    Invariant { name: String, expression: String },
    Program { contract: Contract },
    Logic { body: String, contract: Contract },
}

pub fn spec_kind(a: Attributes<'_>) -> Result<Spec, SpecAttrError> {
    use SpecAttrError::*;
    let mut contract = Contract::new();
    let mut logic = None;

    for attr in a {
        if attr.is_doc_comment() {
            continue;
        }
        let attr = attr.get_normal_item();

        if !is_attr(attr, "spec") {
            continue;
        }

        match attr.path.segments[2].ident.to_string().as_str() {
            "invariant" => {
                assert!(contract.is_empty());

                return Ok(Spec::Invariant {
                    name: invariant_name(attr),
                    expression: ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?,
                });
            }
            "requires" => {
                contract.requires.push(ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?)
            }
            "ensures" => {
                contract.ensures.push(ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?)
            }
            "variant" => {
                contract.variant =
                    Some(ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?)
            }
            "logic" => logic = Some(ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?),
            kind => return Err(UnknownAttribute(kind.into())),
        }
    }
    if let Some(body) = logic {
        Ok(Spec::Logic { body, contract })
    } else {
        Ok(Spec::Program { contract })
    }
}

pub fn is_spec_id(tcx: TyCtxt<'_>, def_id: DefId) -> Result<bool, SpecAttrError> {
    match spec_kind(tcx.get_attrs(def_id))? {
        Spec::Invariant { .. } => Ok(true),
        Spec::Logic { .. } => Ok(true),
        _ => Ok(false),
    }
}

use rustc_ast::AttrItem;

fn is_attr(attr: &AttrItem, str: &str) -> bool {
    let segments = &attr.path.segments;
    segments.len() >= 2
        && segments[0].ident.as_str() == "creusot"
        && segments[1].ident.as_str() == str
}
