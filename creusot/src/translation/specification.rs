use std::collections::HashSet;

use proc_macro2::TokenStream;
use rustc_middle::mir::{Body, SourceInfo};
use syn::{visit::Visit, visit, term::*, BinOp, term::Term::*, PatIdent};

use quote::quote;

use crate::mlcfg::Exp;
use crate::mlcfg::LocalIdent;

pub fn requires_to_why<'tcx>(body: &Body<'tcx>, attr_val: String) -> String {
    let p: Term = syn::parse_str(&attr_val).unwrap();

    let subst =
        body.var_debug_info.iter().take(body.arg_count).map(|vdi| {
            let loc = vdi.place.as_local().unwrap();
            let source_name = vdi.name.to_string();
            let outer_name = format!("{}_o", source_name);
            (LocalIdent::Name(source_name), Exp::Var(LocalIdent::Local(loc, Some(outer_name))))
        }).collect();

    let mut e = to_exp(&p);
    e.subst(subst);
    format!("{}", e)
}

pub fn invariant_to_why<'tcx>(body: &Body<'tcx>, info: SourceInfo, attr_val: String) -> String {
    let p: Term = syn::parse_str(&attr_val).unwrap();
    let mut e = to_exp(&p);
    let fvs = e.fvs();

    let vars_in_scope: Vec<_> =
        body.var_debug_info.iter().filter(|vdi| vdi.source_info.scope <= info.scope).collect();

    // TODO: ensure only one match
    let subst = fvs.iter().map(|free| {
        let var_info =
            vars_in_scope.iter().filter(|vdi| free.to_string() == vdi.name.to_ident_string()).next().unwrap();

        let loc = var_info.place.as_local().unwrap();
        (free.clone(), LocalIdent::Local(loc, Some(var_info.name.to_string())).into())
    }).collect();

    e.subst(subst);
    format!("{}", e)
}

pub fn ensures_to_why<'tcx>(body: &Body<'tcx>, attr_val: String) -> String {
    requires_to_why(body, attr_val)
}


fn bin_to_bin(op: &syn::BinOp) -> Option<rustc_middle::mir::BinOp> {
    use rustc_middle::mir::BinOp::*;

    match op {
        BinOp::Add(_) => { Some(Add) }
        BinOp::Sub(_) => { Some(Sub) }
        BinOp::Mul(_) => { Some(Mul) }
        BinOp::Div(_) => { Some(Div) }
        BinOp::Rem(_) => { Some(Rem) }
        // BinOp::And(_) => { And}
        // BinOp::Or(_) =>  { Or }
        BinOp::BitXor(_) => { Some(BitXor) }
        BinOp::BitAnd(_) => { Some(BitAnd) }
        BinOp::BitOr(_) => { Some(BitOr) }
        BinOp::Shl(_) => { Some(Shl) }
        BinOp::Shr(_) => { Some(Shr) }
        BinOp::Eq(_) => { Some(Eq) }
        BinOp::Lt(_) => { Some(Lt) }
        BinOp::Le(_) => { Some(Le) }
        BinOp::Ne(_) => { Some(Ne) }
        BinOp::Ge(_) => { Some(Ge) }
        BinOp::Gt(_) => { Some(Gt) }
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
        Lit(TermLit { lit }) => {
            match lit {
                syn::Lit::Int(lit) => {
                    Const(crate::mlcfg::Constant(lit.base10_digits().to_owned(), ()))
                }
                syn::Lit::Float(lit) => {
                    Const(crate::mlcfg::Constant(lit.base10_digits().to_owned(), ()))
                }
                syn::Lit::Bool(lit) => {
                    Const(crate::mlcfg::Constant(format!("{}", lit.value), ()))
                }
                _ => unimplemented!(),
            }
        }
        Unary(TermUnary { op, expr }) => {
            let e = to_exp(expr);

            match op {
                syn::UnOp::Deref(_) => {
                    Current(box e)
                }
                syn::UnOp::Not(_) => unimplemented!(),
                syn::UnOp::Neg(_) => unimplemented!(),
            }
        }
        Term::Final(TermFinal { term, .. }) => {
            Final(box to_exp(term))
        }
        Path(TermPath { path, .. }) => {
            path_to_exp(path)
        }
        Paren(TermParen { expr, .. }) => {
            to_exp(expr)
        }
        // Match(_) => {}
        // Paren(_) => {}
        // Impl(TermImpl { hyp, cons, .. }) => {}
        // Forall(TermForall { args, term, .. }) => {}
        // Exists(TermExists { args, term, .. }) => {}
        _ => unimplemented!("{:?}", p),
    }
}

fn path_to_exp(path: &syn::Path) -> crate::mlcfg::Exp {
    if path.segments.len() == 1 {
        Exp::Var(LocalIdent::Name(path.segments[0].ident.to_string()))
    } else {
        panic!()
    }
}
