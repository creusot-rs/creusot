// Translation of Rust types to WhyML
use crate::{
    ctx::TranslationCtx,
    util::{self, get_builtin, item_name, item_qname},
};
use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{
        subst::{Subst, SubstsRef},
        EarlyBinder,
    },
    resolve::Namespace,
    span::{Span, Symbol},
};
use rustc_middle::ty::{ProjectionTy, Ty, TyKind};
use why3::{ty::Type, Ident, QName};

use super::clone_map2::Names;

#[derive(Copy, Clone, PartialEq, Eq)]
enum TyTranslation {
    Declaration,
    Usage,
}

pub(crate) fn translate_ty<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &Names<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
) -> Type {
    translate_ty_inner(TyTranslation::Usage, ctx, names, span, ty)
}

fn translate_ty_inner<'tcx>(
    trans: TyTranslation,
    ctx: &mut TranslationCtx<'tcx>,
    names: &Names<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
) -> Type {
    match ty.kind() {
        TyKind::Bool => Type::Bool,
        TyKind::Char => {
            ctx.warn(span, "support for string types is partial and experimental, expect to encounter limitations.");
            Type::Char
        }
        TyKind::Int(ity) => intty_to_ty(ctx, ity),
        TyKind::Uint(uity) => uintty_to_ty(ctx, uity),
        TyKind::Float(flty) => floatty_to_ty(flty),
        TyKind::Adt(def, s) => {
            if def.is_box() {
                return translate_ty_inner(trans, ctx, names, span, s[0].expect_ty());
            }

            let cons = if let Some(builtin) =
                get_builtin(ctx.tcx, def.did()).and_then(|a| QName::from_string(&a.as_str()))
            {
                Type::TConstructor(builtin.without_search_path())
            } else {
                Type::TConstructor(item_qname(ctx, def.did(), Namespace::TypeNS))
            };

            let args = s.types().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();

            Type::TApp(box cons, args)
        }
        TyKind::Tuple(ref args) => {
            let tys =
                (*args).iter().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();
            Type::Tuple(tys)
        }
        TyKind::Param(p) => {
            if let TyTranslation::Declaration = trans {
                Type::TVar(Ident::build(&p.to_string().to_lowercase()))
            } else {
                Type::TConstructor(QName::from_string(&p.to_string().to_lowercase()).unwrap())
            }
        }
        TyKind::Projection(pty) => {
            if matches!(trans, TyTranslation::Declaration) {
                ctx.crash_and_error(span, "associated types are unsupported in type declarations")
            } else {
                Type::TConstructor(names.get((pty.item_def_id, pty.substs)))
            }
        }
        TyKind::Ref(_, ty, borkind) => {
            use creusot_rustc::ast::Mutability::*;
            match borkind {
                Mut => Type::MutableBorrow(box translate_ty_inner(trans, ctx, names, span, *ty)),
                Not => translate_ty_inner(trans, ctx, names, span, *ty),
            }
        }
        TyKind::Slice(ty) => Type::TApp(
            box Type::TConstructor("seq".into()),
            vec![translate_ty_inner(trans, ctx, names, span, *ty)],
        ),
        TyKind::Array(ty, _) => Type::TApp(
            box Type::TConstructor("rust_array".into()),
            vec![translate_ty_inner(trans, ctx, names, span, *ty)],
        ),
        TyKind::Str => {
            ctx.warn(span, "support for string types is partial and experimental, expect to encounter limitations.");
            Type::TConstructor("string".into())
        }
        // Slice()
        TyKind::Never => Type::Tuple(vec![]),
        TyKind::RawPtr(_) => Type::TConstructor(QName::from_string("opaque_ptr").unwrap()),
        TyKind::Closure(id, subst) => {
            if util::is_logic(ctx.tcx, *id) {
                return Type::Tuple(Vec::new());
            }

            let name = item_name(ctx.tcx, *id, Namespace::TypeNS).to_string().to_lowercase();

            Type::TConstructor(names.get((*id, subst)))
        }
        TyKind::FnDef(_, _) =>
        /* FnDef types are effectively singleton types, so it is sound to translate to unit. */
        {
            Type::Tuple(vec![])
        }
        // Foreign(_) => todo!(),
        // // FnPtr(_) => todo!(),
        // FnPtr(_) => Type::Tuple(vec![]),
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

pub(crate) fn intty_to_ty(
    ctx: &TranslationCtx<'_>,
    ity: &creusot_rustc::middle::ty::IntTy,
) -> Type {
    use creusot_rustc::middle::ty::IntTy::*;

    if !ctx.opts.bounds_check {
        return Type::Integer;
    }

    match ity {
        Isize => isize_ty(),
        I8 => i8_ty(),
        I16 => i16_ty(),
        I32 => i32_ty(),
        I64 => i64_ty(),
        I128 => i128_ty(),
    }
}

pub(crate) fn uintty_to_ty(
    ctx: &TranslationCtx<'_>,
    ity: &creusot_rustc::middle::ty::UintTy,
) -> Type {
    use creusot_rustc::middle::ty::UintTy::*;

    if !ctx.opts.bounds_check {
        return Type::Integer;
    }

    match ity {
        Usize => usize_ty(),
        U8 => u8_ty(),
        U16 => u16_ty(),
        U32 => u32_ty(),
        U64 => u64_ty(),
        U128 => u128_ty(),
    }
}

pub(crate) fn floatty_to_ty(fty: &creusot_rustc::middle::ty::FloatTy) -> Type {
    use creusot_rustc::middle::ty::FloatTy::*;

    match fty {
        F32 => single_ty(),
        F64 => double_ty(),
    }
}

pub(crate) fn double_ty() -> Type {
    Type::TConstructor(QName::from_string("Float64.t").unwrap())
}

pub(crate) fn single_ty() -> Type {
    Type::TConstructor(QName::from_string("Float32.t").unwrap())
}

pub(crate) fn u8_ty() -> Type {
    Type::TConstructor(QName::from_string("uint8").unwrap())
}

pub(crate) fn u16_ty() -> Type {
    Type::TConstructor(QName::from_string("uint16").unwrap())
}

pub(crate) fn u32_ty() -> Type {
    Type::TConstructor(QName::from_string("uint32").unwrap())
}

pub(crate) fn u64_ty() -> Type {
    Type::TConstructor(QName::from_string("uint64").unwrap())
}

pub(crate) fn u128_ty() -> Type {
    Type::TConstructor(QName::from_string("uint128").unwrap())
}

pub(crate) fn usize_ty() -> Type {
    Type::TConstructor(QName::from_string("usize").unwrap())
}

pub(crate) fn i8_ty() -> Type {
    Type::TConstructor(QName::from_string("int8").unwrap())
}

pub(crate) fn i16_ty() -> Type {
    Type::TConstructor(QName::from_string("int16").unwrap())
}

pub(crate) fn i32_ty() -> Type {
    Type::TConstructor(QName::from_string("int32").unwrap())
}

pub(crate) fn i64_ty() -> Type {
    Type::TConstructor(QName::from_string("int64").unwrap())
}

pub(crate) fn i128_ty() -> Type {
    Type::TConstructor(QName::from_string("int128").unwrap())
}

pub(crate) fn isize_ty() -> Type {
    Type::TConstructor(QName::from_string("isize").unwrap())
}
