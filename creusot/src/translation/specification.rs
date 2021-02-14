use crate::mlcfg::printer::FormatEnv;
use crate::mlcfg::Exp;
use crate::mlcfg::LocalIdent;
use crate::mlcfg::QName;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::{Body, SourceInfo}, ty::TyCtxt};
use syn::{term::Term::*, term::*, BinOp};

// Check if a set of invariants includes an invariant tag, indicating the associated body is
// an invariant closure and should be ignored by translation
pub fn get_invariant(attrs: &[Attribute]) -> Result<Option<(String, String)>, SpecAttrError> {
    let specs = spec_attrs(attrs)?;
    if specs.len() != 1 {
        return Ok(None)
    }

    if let Invariant { name, expression} = spec_attrs(attrs)?.remove(0) {
        Ok(Some((name, expression)))
    } else {
        Ok(None)
    }
}

pub fn is_spec_id(tcx: TyCtxt<'_>, did: DefId) -> Result<bool, SpecAttrError> {
    let attrs = tcx.get_attrs(did);
    Ok(!spec_attrs(attrs)?.is_empty())
}

pub fn translate_contract(attrs: &[Attribute], body: &Body) -> (Vec<String>, Vec<String>) {
    let mut func_contract = (Vec::new(), Vec::new());

    for spec_item in spec_attrs(attrs).unwrap() {
        match spec_item {
            Requires { expression } => func_contract.0.push(requires_to_why(&body, expression)),
            Ensures { expression } => func_contract.1.push(ensures_to_why(&body, expression)),
            _ => panic!("Unexpected spec item in contract position!"),
        }
    }
    func_contract
}

pub fn requires_to_why(body: &Body<'_>, attr_val: String) -> String {
    let p: Term = syn::parse_str(&attr_val).unwrap();
    use rustc_middle::mir::VarDebugInfoContents::Place;
    let subst = body
        .var_debug_info
        .iter()
        .take(body.arg_count)
        .map(|vdi| {
            let loc = match vdi.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!()
            };
            let source_name = vdi.name.to_string();
            let outer_name = format!("o_{}", source_name);
            (LocalIdent::Name(source_name), Exp::Var(LocalIdent::Local(loc, Some(outer_name))))
        })
        .collect();

    let mut e = to_exp(&p);
    e.subst(subst);
    format!("{}", FormatEnv { scope: &[], indent: 0 }.to(&e))
}

pub fn invariant_to_why(body: &Body<'_>, info: SourceInfo, attr_val: String) -> String {
    let p: Term = syn::parse_str(&attr_val).unwrap();
    let mut e = to_exp(&p);
    let fvs = e.fvs();

    let vars_in_scope: Vec<_> =
        body.var_debug_info.iter().filter(|vdi| vdi.source_info.scope <= info.scope).collect();
    use rustc_middle::mir::VarDebugInfoContents::Place;

    // TODO: ensure only one match
    let subst = fvs
        .iter()
        .map(|free| {
            let var_info = vars_in_scope
                .iter()
                .find(|vdi| free.to_string() == vdi.name.to_ident_string())
                .unwrap();

            let loc = match var_info.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!()
            };
            (free.clone(), LocalIdent::Local(loc, Some(var_info.name.to_string())).into())
        })
        .collect();

    e.subst(subst);
    format!("{}", FormatEnv { scope: &[], indent: 0 }.to(&e))
}

pub fn ensures_to_why(body: &Body<'_>, attr_val: String) -> String {
    requires_to_why(body, attr_val)
}

fn bin_to_bin(op: &syn::BinOp) -> Option<crate::mlcfg::FullBinOp> {
    use crate::mlcfg::FullBinOp::*;
    use rustc_middle::mir::BinOp::*;

    match op {
        BinOp::Add(_) => Some(Other(Add)),
        BinOp::Sub(_) => Some(Other(Sub)),
        BinOp::Mul(_) => Some(Other(Mul)),
        BinOp::Div(_) => Some(Other(Div)),
        BinOp::Rem(_) => Some(Other(Rem)),
        BinOp::And(_) => Some(And),
        BinOp::Or(_) => Some(Or),
        BinOp::BitXor(_) => Some(Other(BitXor)),
        BinOp::BitAnd(_) => Some(Other(BitAnd)),
        BinOp::BitOr(_) => Some(Other(BitOr)),
        BinOp::Shl(_) => Some(Other(Shl)),
        BinOp::Shr(_) => Some(Other(Shr)),
        BinOp::Eq(_) => Some(Other(Eq)),
        BinOp::Lt(_) => Some(Other(Lt)),
        BinOp::Le(_) => Some(Other(Le)),
        BinOp::Ne(_) => Some(Other(Ne)),
        BinOp::Ge(_) => Some(Other(Ge)),
        BinOp::Gt(_) => Some(Other(Gt)),
        _ => None,
    }
}

fn to_exp(p: &Term) -> crate::mlcfg::Exp {
    use crate::mlcfg::Exp::*;
    match p {
        Binary(TermBinary { left, right, op, .. }) => {
            let op = bin_to_bin(op).unwrap();
            BinaryOp(op, box to_exp(left), box to_exp(right))
        }
        // Block(_) => {}
        // Cast(_) => {}
        // Field(_) => {}
        // Group(_) => {}
        // If(_) => {}
        Lit(TermLit { lit }) => match lit {
            syn::Lit::Int(lit) => {
                Const(crate::mlcfg::Constant::Other(lit.base10_digits().to_owned()))
            }
            syn::Lit::Float(lit) => {
                Const(crate::mlcfg::Constant::Other(lit.base10_digits().to_owned()))
            }
            syn::Lit::Bool(lit) => Const(crate::mlcfg::Constant::Other(format!("{}", lit.value))),
            _ => unimplemented!(),
        },
        Unary(TermUnary { op, expr }) => {
            let e = to_exp(expr);

            match op {
                syn::UnOp::Deref(_) => Current(box e),
                syn::UnOp::Not(_) => unimplemented!(),
                syn::UnOp::Neg(_) => unimplemented!(),
            }
        }
        Term::Final(TermFinal { term, .. }) => Final(box to_exp(term)),
        Path(TermPath { path, .. }) => path_to_exp(path),
        Paren(TermParen { expr, .. }) => to_exp(expr),
        // Match(_) => {}
        Term::Impl(TermImpl { hyp, cons, .. }) => Exp::Impl(box to_exp(hyp), box to_exp(cons)),
        Term::Forall(TermForall { args, term, .. }) => {
            let binders = args
                .iter()
                .map(|qa| (LocalIdent::Name(qa.ident.to_string()), from_ty(&qa.ty)))
                .collect();

            Exp::Forall(binders, box to_exp(term))
        }
        Term::Exists(TermExists { args, term, .. }) => {
            let binders = args
                .iter()
                .map(|qa| (LocalIdent::Name(qa.ident.to_string()), from_ty(&qa.ty)))
                .collect();

            Exp::Exists(binders, box to_exp(term))
        }
        _ => unimplemented!("{:?}", p),
    }
}

fn from_ty(ty: &syn::Type) -> crate::mlcfg::Type {
    use crate::mlcfg::Type::*;
    use syn::*;

    match ty {
        syn::Type::Paren(TypeParen { elem, .. }) => from_ty(elem),
        syn::Type::Path(TypePath { path, .. }) => type_path_to_type(path),
        syn::Type::Reference(TypeReference { mutability, elem, .. }) => {
            if mutability.is_some() {
                MutableBorrow(box from_ty(elem))
            } else {
                from_ty(elem)
            }
        }
        syn::Type::Tuple(TypeTuple { elems, .. }) => {
            crate::mlcfg::Type::Tuple(elems.iter().map(from_ty).collect())
        }
        syn::Type::Never(_) => unimplemented!("never type"),

        syn::Type::Array(_) | syn::Type::Slice(_) => unimplemented!("array / slice"),
        syn::Type::BareFn(_) => unimplemented!("bare fn"),
        syn::Type::ImplTrait(_) | syn::Type::TraitObject(_) => unimplemented!("trait objects"),
        syn::Type::Infer(_) => unimplemented!("infer"),
        syn::Type::Group(_) => unimplemented!("groupe"),
        _ => unimplemented!("unsupported type kind"),
    }
}

fn type_path_to_type(path: &syn::Path) -> crate::mlcfg::Type {
    use crate::mlcfg::Type;
    use rustc_middle::ty::{IntTy::*, UintTy::*};
    match path.segments[0].ident.to_string().as_str() {
        "u8" => Type::Uint(U8),
        "u16" => Type::Uint(U16),
        "u32" => Type::Uint(U32),
        "u64" => Type::Uint(U64),
        "u128" => Type::Uint(U128),
        "usize" => Type::Uint(Usize),

        "i8" => Type::Int(I8),
        "i16" => Type::Int(I16),
        "i32" => Type::Int(I32),
        "i64" => Type::Int(I64),
        "i18" => Type::Int(I128),
        "isize" => Type::Int(Isize),

        _ => Type::TConstructor(QName {
            module: vec![],
            name: path.segments.iter().map(|s| s.ident.to_string()).collect(),
        }),
    }
}

fn path_to_exp(path: &syn::Path) -> crate::mlcfg::Exp {
    if path.segments.len() == 1 {
        Exp::Var(LocalIdent::Name(path.segments[0].ident.to_string()))
    } else {
        panic!()
    }
}

use rustc_ast::{
    token::TokenKind::Literal,
    tokenstream::{TokenStream, TokenTree::*},
    Attribute,
};
use rustc_middle::ty::Attributes;

fn ts_to_symbol(ts: TokenStream) -> Option<String> {
    assert_eq!(ts.len(), 1);

    if let Token(tok) = ts.trees().next().unwrap() {
        if let Literal(lit) = tok.kind {
            return Some(unescape::unescape(&lit.symbol.as_str())?);
        }
    }
    None
}

fn invariant_name(attr: &rustc_ast::AttrItem) -> String {
    attr.path.segments[3].ident.name.to_string()
}

pub enum SpecItem {
    Invariant { name: String, expression: String },
    Requires { expression: String },
    Ensures { expression: String },
}

#[derive(Debug)]
pub enum SpecAttrError {
    UnknownAttribute(String),
    InvalidTokens,
}

use SpecItem::*;

pub fn spec_attrs(a: Attributes<'_>) -> Result<Vec<SpecItem>, SpecAttrError> {
    use SpecAttrError::*;
    let mut res = Vec::new();
    for attr in a {
        if attr.is_doc_comment() {
            continue;
        }
        let attr = attr.get_normal_item();
        if !is_attr(attr, "spec") {
            continue;
        }
        match attr.path.segments[2].ident.to_string().as_str() {
            "invariant" => res.push(Invariant {
                name: invariant_name(attr),
                expression: ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?,
            }),
            "requires" => res.push(Requires {
                expression: ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?,
            }),
            "ensures" => res.push(Ensures {
                expression: ts_to_symbol(attr.args.inner_tokens()).ok_or(InvalidTokens)?,
            }),
            kind => Err(UnknownAttribute(kind.into()))?,
        }
    }
    Ok(res)
}

use rustc_ast::AttrItem;

fn is_attr(attr: &AttrItem, str: &str) -> bool {
    let segments = &attr.path.segments;
    segments.len() >= 2
        && segments[0].ident.as_str() == "creusot"
        && segments[1].ident.as_str() == str
}
