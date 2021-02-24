use crate::mlcfg::QName;
use rustc_hir::def_id::DefId;

use rustc_middle::ty::TyCtxt;

use pearlite::term;
use pearlite::term::Name;

use crate::mlcfg::{self, Exp};

pub fn lower_term_to_why(tcx: TyCtxt<'_>, t: term::Term) -> Exp {
    use term::Term::*;
    match t {
        Match { box expr, arms } => Exp::Match(
            box lower_term_to_why(tcx, expr),
            arms.into_iter().map(|t| lower_arm_to_why(tcx, t)).collect(),
        ),
        Binary { box left, op: pearlite::term::BinOp::Impl, box right } => {
            Exp::Impl(box lower_term_to_why(tcx, left), box lower_term_to_why(tcx, right))
        }
        Binary { box left, op, box right } => {
            let op = op_to_op(op);
            Exp::BinaryOp(op, box lower_term_to_why(tcx, left), box lower_term_to_why(tcx, right))
        }
        Unary { op, box expr } => {
            let expr = box lower_term_to_why(tcx, expr);
            match op {
                term::UnOp::Final => Exp::Final(expr),
                term::UnOp::Current => Exp::Current(expr),
                term::UnOp::Neg => Exp::UnaryOp(rustc_middle::mir::UnOp::Neg, expr),
                term::UnOp::Not => Exp::UnaryOp(rustc_middle::mir::UnOp::Not, expr),
            }
        }
        Variable { path } => match path {
            Name::Path { .. } => Exp::QVar(lower_value_path(tcx, path)),
            Name::Ident(i) => Exp::Var(i.into()),
        },
        Call { func, args } => {
            let is_c = is_constructor(tcx, &func);
            let name = lower_value_path(tcx, func);
            let args = args.into_iter().map(|t| lower_term_to_why(tcx, t)).collect();

            if is_c {
                Exp::Constructor { ctor: name, args }
            } else {
                Exp::Call(box Exp::QVar(name), args)
            }
        }
        Lit { lit } => Exp::Const(lit_to_const(lit)),
        Forall { args, box body } => {
            let args = args.into_iter().map(|(i, t)| (i.0.into(), lower_type_to_why(tcx, t))).collect();

            Exp::Forall(args, box lower_term_to_why(tcx, body))
        }
        Exists { args, box body } => {
            let args = args.into_iter().map(|(i, t)| (i.0.into(), lower_type_to_why(tcx, t))).collect();

            Exp::Exists(args, box lower_term_to_why(tcx, body))
        }
        Let { pat, box arg, box body } => Exp::Let {
            pattern: lower_pattern_to_why(tcx, pat),
            arg: box lower_term_to_why(tcx, arg),
            body: box lower_term_to_why(tcx, body),
        },
        Absurd => Exp::Absurd,
        Cast { box expr, ty: _ } => lower_term_to_why(tcx, expr),
        Tuple { elems } => {
            Exp::Tuple(elems.into_iter().map(|t| lower_term_to_why(tcx, t)).collect())
        }
    }
}

pub fn lower_type_to_why(tcx: TyCtxt<'_>, ty: pearlite::term::Type) -> crate::mlcfg::Type {
    use crate::mlcfg::Type::*;
    use pearlite::term::*;

    match ty {
        term::Type::Path { path } => TConstructor(lower_type_path(tcx, path)),
        term::Type::Reference { kind: RefKind::Mut, box ty } => {
            MutableBorrow(box lower_type_to_why(tcx, ty))
        }
        term::Type::Reference { kind: _, box ty } => lower_type_to_why(tcx, ty),
        term::Type::Tuple { elems } => Tuple(elems.into_iter().map(|t| lower_type_to_why(tcx, t)).collect()),
        term::Type::Lit(lit) => {
            use pearlite::term::Size::*;
            use rustc_middle::ty::{FloatTy::*, IntTy::*, UintTy::*};

            match lit {
                term::LitTy::Signed(s) => match s {
                    Eight => Int(I8),
                    Sixteen => Int(I16),
                    ThirtyTwo => Int(I32),
                    SixtyFour => Int(I64),
                    Mach => Int(Isize),
                    Unknown => {
                        unimplemented!("integers")
                    }
                },
                term::LitTy::Unsigned(s) => match s {
                    Eight => Uint(U8),
                    Sixteen => Uint(U16),
                    ThirtyTwo => Uint(U32),
                    SixtyFour => Uint(U64),
                    Mach => Uint(Usize),
                    Unknown => {
                        unimplemented!("uintegers")
                    }
                },
                term::LitTy::Integer => Integer,
                term::LitTy::Float => Float(F32),
                term::LitTy::Double => Float(F64),
                term::LitTy::Boolean => Bool,
            }
        }
        term::Type::App { box func, args } => {
            TApp(box lower_type_to_why(tcx, func), args.into_iter().map(|t| lower_type_to_why(tcx, t)).collect())
        }
        term::Type::Function { args, box res } => args
            .into_iter()
            .rfold(lower_type_to_why(tcx, res), |acc, arg| TFun(box lower_type_to_why(tcx, arg), box acc)),
        term::Type::Var(tyvar) => TVar(('a'..).nth(tyvar.0 as usize).unwrap().to_string()),
        term::Type::Unknown(_) => {
            panic!()
        } // _ => panic!("{:?}", ty),
    }
}
fn lit_to_const(lit: pearlite::term::Literal) -> crate::mlcfg::Constant {
    use crate::mlcfg::Constant::{self, *};

    match lit {
        term::Literal::U8(u) => Uint(u as u128),
        term::Literal::U16(u) => Uint(u as u128),
        term::Literal::U32(u) => Uint(u as u128),
        term::Literal::U64(u) => Uint(u as u128),
        term::Literal::Usize(u) => Uint(u as u128),
        term::Literal::Int(u) => Int(u as i128),
        term::Literal::F32(_) => {
            unimplemented!()
        }
        term::Literal::F64(_) => {
            unimplemented!()
        }
        term::Literal::Bool(b) => {
            if b {
                Constant::const_true()
            } else {
                Constant::const_false()
            }
        }
    }
}

fn op_to_op(op: term::BinOp) -> mlcfg::FullBinOp {
    use mlcfg::FullBinOp::*;
    use rustc_middle::mir::BinOp;
    match op {
        term::BinOp::Add => Other(BinOp::Add),
        term::BinOp::Sub => Other(BinOp::Sub),
        term::BinOp::Mul => Other(BinOp::Mul),
        term::BinOp::Div => Other(BinOp::Div),
        term::BinOp::Eq => Other(BinOp::Eq),
        term::BinOp::Ne => Other(BinOp::Ne),
        term::BinOp::Le => Other(BinOp::Le),
        term::BinOp::Ge => Other(BinOp::Ge),
        term::BinOp::Gt => Other(BinOp::Gt),
        term::BinOp::Lt => Other(BinOp::Lt),
        term::BinOp::And => And,
        term::BinOp::Or => Or,
        term::BinOp::Impl => {
            panic!()
        }
    }
}

fn lower_arm_to_why(tcx: TyCtxt<'_>, a: term::MatchArm) -> (mlcfg::Pattern, Exp) {
    (lower_pattern_to_why(tcx, a.pat), lower_term_to_why(tcx, *a.body))
}

fn lower_pattern_to_why(tcx: TyCtxt<'_>, p: term::Pattern) -> mlcfg::Pattern {
    use mlcfg::Pattern;
    match p {
        term::Pattern::Var(x) => Pattern::VarP(x.0.into()),
        // term::Pattern::Struct { path, fields } => {}
        term::Pattern::TupleStruct { path, fields } => {
            let name = lower_value_path(tcx, path);
            let fields = fields.into_iter().map(|p| lower_pattern_to_why(tcx, p)).collect();

            Pattern::ConsP(name, fields)
        }
        term::Pattern::Boolean(b) => {
            if b {
                Pattern::mk_true()
            } else {
                Pattern::mk_false()
            }
        }
        term::Pattern::Wild => Pattern::Wildcard,
        _ => {
            unimplemented!()
        }
    }
}

fn is_constructor(tcx: TyCtxt<'_>, path: &Name) -> bool {
    match path {
        Name::Ident(_) => false,
        Name::Path { id, ..} => {
            let kind = tcx.def_kind(super::id_to_def_id(*id));
            use rustc_hir::def::DefKind::*;
            match kind {
                Ctor(_, _) | Variant | Struct => true,
                _ => false,
            }
        }
    }
}

fn lower_value_path(tcx: TyCtxt<'_>, path: Name) -> QName {
    if let Name::Path { id, .. } = path {
        let defid: DefId = super::id_to_def_id(id);
        crate::translation::translate_value_id(tcx, defid)
    } else {
        panic!("cannot lower a local identifier to a qualified name");
    }
}

fn lower_type_path(tcx: TyCtxt<'_>, path: Name) -> QName {
    if let Name::Path { id, .. } = path {
        let defid: DefId = super::id_to_def_id(id);
        crate::translation::translate_type_id(tcx, defid)
    } else {
        panic!("cannot lower a local identifier to a qualified name");
    }
}
