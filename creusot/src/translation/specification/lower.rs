use crate::translation::TranslationCtx;
use pearlite::term::Name;
use pearlite::term::{self, DerefKind, RefKind};
use rustc_hir::def_id::DefId;
use why3::mlcfg::QName;
use why3::mlcfg::{self, Exp};

pub fn lower_term_to_why(ctx: &mut TranslationCtx, t: term::Term) -> Exp {
    use term::Term::*;
    match t {
        Match { box expr, arms } => Exp::Match(
            box lower_term_to_why(ctx, expr),
            arms.into_iter().map(|t| lower_arm_to_why(ctx, t)).collect(),
        ),
        Binary { box left, op: pearlite::term::BinOp::Impl, box right } => {
            Exp::Impl(box lower_term_to_why(ctx, left), box lower_term_to_why(ctx, right))
        }
        Binary { box left, op, box right } => {
            let op = op_to_op(op);
            Exp::BinaryOp(op, box lower_term_to_why(ctx, left), box lower_term_to_why(ctx, right))
        }
        Unary { op, box expr } => {
            let expr = box lower_term_to_why(ctx, expr);
            match op {
                term::UnOp::Final => Exp::Final(expr),
                term::UnOp::Deref(Some(DerefKind::Ref(RefKind::Mut))) => Exp::Current(expr),
                term::UnOp::Deref(Some(_)) => *expr,
                term::UnOp::Deref(None) => unreachable!(),
                term::UnOp::Neg => Exp::UnaryOp(mlcfg::UnOp::Neg, expr),
                term::UnOp::Not => Exp::UnaryOp(mlcfg::UnOp::Not, expr),
            }
        }
        Variable { path } => match path {
            Name::Path { .. } => Exp::QVar(lower_value_path(ctx, path)),
            Name::Ident(i) => Exp::Var(i.into()),
        },
        Call { func, args } => {
            let is_c = is_constructor(ctx, &func);
            let name = lower_value_path(ctx, func);
            let args = args.into_iter().map(|t| lower_term_to_why(ctx, t)).collect();

            if is_c {
                Exp::Constructor { ctor: name, args }
            } else {
                Exp::Call(box Exp::QVar(name), args)
            }
        }
        Lit { lit } => Exp::Const(lit_to_const(lit)),
        Forall { args, box body } => {
            let args =
                args.into_iter().map(|(i, t)| (i.0.into(), lower_type_to_why(ctx, t))).collect();

            Exp::Forall(args, box lower_term_to_why(ctx, body))
        }
        Exists { args, box body } => {
            let args =
                args.into_iter().map(|(i, t)| (i.0.into(), lower_type_to_why(ctx, t))).collect();

            Exp::Exists(args, box lower_term_to_why(ctx, body))
        }
        Let { pat, box arg, box body } => Exp::Let {
            pattern: lower_pattern_to_why(ctx, pat),
            arg: box lower_term_to_why(ctx, arg),
            body: box lower_term_to_why(ctx, body),
        },
        Absurd => Exp::Absurd,
        Cast { box expr, ty: _ } => lower_term_to_why(ctx, expr),
        Tuple { elems } => {
            Exp::Tuple(elems.into_iter().map(|t| lower_term_to_why(ctx, t)).collect())
        }
        If { box cond, box then_branch, box else_branch } => {
            use mlcfg::Pattern;
            Exp::Match(
                box lower_term_to_why(ctx, cond),
                vec![
                    (Pattern::mk_true(), lower_term_to_why(ctx, then_branch)),
                    (Pattern::mk_false(), lower_term_to_why(ctx, else_branch)),
                ],
            )
        }
    }
}

pub fn lower_type_to_why(ctx: &mut TranslationCtx, ty: pearlite::term::Type) -> why3::mlcfg::Type {
    use pearlite::term::*;
    use why3::mlcfg::Type::*;

    match ty {
        term::Type::Path { path } => TConstructor(lower_type_path(ctx, path)),
        term::Type::Box { box ty } => lower_type_to_why(ctx, ty),
        term::Type::Reference { kind: RefKind::Mut, box ty } => {
            MutableBorrow(box lower_type_to_why(ctx, ty))
        }
        term::Type::Reference { kind: _, box ty } => lower_type_to_why(ctx, ty),
        term::Type::Tuple { elems } => {
            Tuple(elems.into_iter().map(|t| lower_type_to_why(ctx, t)).collect())
        }
        term::Type::Lit(lit) => lit_ty_to_ty(lit),
        term::Type::App { box func, args } => TApp(
            box lower_type_to_why(ctx, func),
            args.into_iter().map(|t| lower_type_to_why(ctx, t)).collect(),
        ),
        term::Type::Function { args, box res } => {
            args.into_iter().rfold(lower_type_to_why(ctx, res), |acc, arg| {
                TFun(box lower_type_to_why(ctx, arg), box acc)
            })
        }
        term::Type::Var(tyvar) => TVar(('a'..).nth(tyvar.0 as usize).unwrap().to_string()),
        term::Type::Unknown(_) => {
            panic!()
        } // _ => panic!("{:?}", ty),
    }
}

fn lit_ty_to_ty(litty: pearlite::term::LitTy) -> mlcfg::Type {
    use pearlite::term::Size::*;
    use why3::mlcfg::Type::*;
    use crate::ty::*;

    match litty {
        term::LitTy::Signed(s) => match s {
            Eight => i8_ty(),
            Sixteen => i16_ty(),
            ThirtyTwo => i32_ty(),
            SixtyFour => i64_ty(),
            Mach => isize_ty(),
            Unknown => unimplemented!("integers"),
        },
        term::LitTy::Unsigned(s) => match s {
            Eight => u8_ty(),
            Sixteen => u16_ty(),
            ThirtyTwo => u32_ty(),
            SixtyFour => u64_ty(),
            Mach => usize_ty(),
            Unknown => unimplemented!("integers"),
        },
        term::LitTy::Float => TConstructor(QName { module: vec![], name: vec!["single".into()] }),
        term::LitTy::Double => TConstructor(QName { module: vec![], name: vec!["double".into()] }),
        term::LitTy::Boolean => Bool,
        term::LitTy::Integer => TConstructor(QName { module: vec![], name: vec!["int".into()]})
    }
}

fn lit_to_const(lit: pearlite::term::Literal) -> why3::mlcfg::Constant {
    use why3::mlcfg::Constant::{self, *};
    use crate::ty::*;
    match lit {
        term::Literal::U8(u) => Uint(u as u128, Some(u8_ty())),
        term::Literal::U16(u) => Uint(u as u128, Some(u16_ty())),
        term::Literal::U32(u) => Uint(u as u128, Some(u32_ty())),
        term::Literal::U64(u) => Uint(u as u128, Some(u64_ty())),
        term::Literal::Usize(u) => Uint(u as u128, Some(usize_ty())),
        term::Literal::Int(u) => Int(u as i128, None),
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

fn op_to_op(op: term::BinOp) -> mlcfg::BinOp {
    use mlcfg::BinOp::*;
    match op {
        term::BinOp::Add => Add,
        term::BinOp::Sub => Sub,
        term::BinOp::Mul => Mul,
        term::BinOp::Div => Div,
        term::BinOp::Eq => Eq,
        term::BinOp::Ne => Ne,
        term::BinOp::Le => Le,
        term::BinOp::Ge => Ge,
        term::BinOp::Gt => Gt,
        term::BinOp::Lt => Lt,
        term::BinOp::And => And,
        term::BinOp::Or => Or,
        term::BinOp::Impl => {
            panic!()
        }
    }
}

fn lower_arm_to_why(ctx: &mut TranslationCtx, a: term::MatchArm) -> (mlcfg::Pattern, Exp) {
    (lower_pattern_to_why(ctx, a.pat), lower_term_to_why(ctx, *a.body))
}

fn lower_pattern_to_why(ctx: &mut TranslationCtx, p: term::Pattern) -> mlcfg::Pattern {
    use mlcfg::Pattern;
    match p {
        term::Pattern::Var(x) => Pattern::VarP(x.0.into()),
        // term::Pattern::Struct { path, fields } => {}
        term::Pattern::TupleStruct { path, fields } => {
            let name = lower_value_path(ctx, path);
            let fields = fields.into_iter().map(|p| lower_pattern_to_why(ctx, p)).collect();

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

fn is_constructor(ctx: &mut TranslationCtx, path: &Name) -> bool {
    match path {
        Name::Ident(_) => false,
        Name::Path { id, .. } => {
            let kind = ctx.tcx.def_kind(super::id_to_def_id(*id));
            use rustc_hir::def::DefKind::*;
            match kind {
                Ctor(_, _) | Variant | Struct => true,
                _ => false,
            }
        }
    }
}

fn lower_value_path(ctx: &mut TranslationCtx, path: Name) -> QName {
    if let Name::Path { id, .. } = path {
        let defid: DefId = super::id_to_def_id(id);
        crate::translation::translate_value_id(ctx.tcx, defid)
    } else {
        panic!("cannot lower a local identifier to a qualified name");
    }
}

fn lower_type_path(ctx: &mut TranslationCtx, path: Name) -> QName {
    if let Name::Path { id, .. } = path {
        let defid: DefId = super::id_to_def_id(id);
        crate::ty::translate_ty_name(ctx, defid)
    } else {
        panic!("cannot lower a local identifier to a qualified name");
    }
}
