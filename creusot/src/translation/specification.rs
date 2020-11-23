use rustc_middle::mir::{Body, SourceInfo};
use syn::{term::Term::*, term::*, BinOp};
use crate::mlcfg::Exp;
use crate::mlcfg::LocalIdent;
use crate::mlcfg::QName;

pub fn requires_to_why<'tcx>(body: &Body<'tcx>, attr_val: String) -> String {
    let p: Term = syn::parse_str(&attr_val).unwrap();

    let subst = body
        .var_debug_info
        .iter()
        .take(body.arg_count)
        .map(|vdi| {
            let loc = vdi.place.as_local().unwrap();
            let source_name = vdi.name.to_string();
            let outer_name = format!("o_{}", source_name);
            (LocalIdent::Name(source_name), Exp::Var(LocalIdent::Local(loc, Some(outer_name))))
        })
        .collect();

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
    let subst = fvs
        .iter()
        .map(|free| {
            let var_info = vars_in_scope
                .iter()
                .filter(|vdi| free.to_string() == vdi.name.to_ident_string())
                .next()
                .unwrap();

            let loc = var_info.place.as_local().unwrap();
            (free.clone(), LocalIdent::Local(loc, Some(var_info.name.to_string())).into())
        })
        .collect();

    e.subst(subst);
    format!("{}", e)
}

pub fn ensures_to_why<'tcx>(body: &Body<'tcx>, attr_val: String) -> String {
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
            syn::Lit::Int(lit) => Const(crate::mlcfg::Constant(lit.base10_digits().to_owned(), ())),
            syn::Lit::Float(lit) => {
                Const(crate::mlcfg::Constant(lit.base10_digits().to_owned(), ()))
            }
            syn::Lit::Bool(lit) => Const(crate::mlcfg::Constant(format!("{}", lit.value), ())),
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
            if let Some(_) = mutability {
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
    use rustc_ast::ast::{IntTy::*, UintTy::*};
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
            segments: path.segments.iter().map(|s| s.ident.to_string()).collect(),
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
