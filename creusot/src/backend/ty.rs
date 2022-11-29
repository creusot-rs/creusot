use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{
        self,
        subst::{InternalSubsts, SubstsRef},
        ClosureSubsts, FieldDef, ProjectionTy, Ty, TyCtxt, VariantDef,
    },
    resolve::Namespace,
    span::{Span, Symbol, DUMMY_SP},
    type_ir::sty::TyKind::*,
};
use indexmap::IndexSet;
use std::collections::VecDeque;
use why3::{
    declaration::{
        AdtDecl, ConstructorDecl, Contract, Decl, Field, LetDecl, LetKind, Module, Signature,
    },
    exp::{Binder, Exp, Pattern},
    Ident,
};

use why3::{declaration::TyDecl, ty::Type as MlT, QName};

use crate::{
    ctx::*,
    translation::ty::translate_ty_param,
    util::{self, constructor_qname, get_builtin, item_name, item_qname},
};

use super::{clone_map2::Names, Cloner};

#[derive(Copy, Clone, PartialEq, Eq)]
enum TyTranslation {
    Declaration,
    Usage,
}

// Translate a type usage
pub(crate) fn translate_ty<'tcx, C: Cloner<'tcx>>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut C,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    translate_ty_inner(TyTranslation::Usage, ctx, names, span, ty)
}

fn translate_ty_inner<'tcx, C: Cloner<'tcx>>(
    trans: TyTranslation,
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut C,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    match ty.kind() {
        Bool => MlT::Bool,
        Char => {
            ctx.warn(span, "support for string types is partial and experimental, expect to encounter limitations.");
            MlT::Char
        }
        Int(ity) => intty_to_ty(ity),
        Uint(uity) => uintty_to_ty(uity),
        Float(flty) => floatty_to_ty(flty),
        Adt(def, s) => {
            if def.is_box() {
                return translate_ty_inner(trans, ctx, names, span, s[0].expect_ty());
            }

            if Some(def.did()) == ctx.tcx.get_diagnostic_item(Symbol::intern("creusot_int")) {
                return MlT::Integer;
            }

            let cons = if let Some(builtin) =
                get_builtin(ctx.tcx, def.did()).and_then(|a| QName::from_string(&a.as_str()))
            {
                MlT::TConstructor(builtin.without_search_path())
            } else {
                ctx.translate(def.did());
                MlT::TConstructor(item_qname(ctx, def.did(), Namespace::TypeNS))
            };

            let args = s.types().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();

            MlT::TApp(box cons, args)
        }
        Tuple(ref args) => {
            let tys =
                (*args).iter().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();
            MlT::Tuple(tys)
        }
        Param(p) => {
            if let TyTranslation::Declaration = trans {
                MlT::TVar(translate_ty_param(p.name))
            } else {
                MlT::TConstructor(QName::from_string(&p.to_string().to_lowercase()).unwrap())
            }
        }
        Projection(pty) => {
            if matches!(trans, TyTranslation::Declaration) {
                ctx.crash_and_error(span, "associated types are unsupported in type declarations")
            } else {
                translate_projection_ty(ctx, names, pty)
            }
        }
        Ref(_, ty, borkind) => {
            use creusot_rustc::ast::Mutability::*;
            match borkind {
                Mut => MlT::MutableBorrow(box translate_ty_inner(trans, ctx, names, span, *ty)),
                Not => translate_ty_inner(trans, ctx, names, span, *ty),
            }
        }
        Slice(ty) => MlT::TApp(
            box MlT::TConstructor("seq".into()),
            vec![translate_ty_inner(trans, ctx, names, span, *ty)],
        ),
        Array(ty, _) => MlT::TApp(
            box MlT::TConstructor("rust_array".into()),
            vec![translate_ty_inner(trans, ctx, names, span, *ty)],
        ),
        Str => {
            ctx.warn(span, "support for string types is partial and experimental, expect to encounter limitations.");
            MlT::TConstructor("string".into())
        }
        // Slice()
        Never => MlT::Tuple(vec![]),
        RawPtr(_) => MlT::TConstructor(QName::from_string("opaque_ptr").unwrap()),
        Closure(id, subst) => {
            ctx.translate(*id);

            if util::is_logic(ctx.tcx, *id) {
                return MlT::Tuple(Vec::new());
            }

            let name = item_name(ctx.tcx, *id, Namespace::TypeNS).to_string().to_lowercase();
            let cons = MlT::TConstructor(names.ty(*id, subst));

            cons
        }
        FnDef(_, _) =>
        /* FnDef types are effectively singleton types, so it is sound to translate to unit. */
        {
            MlT::Tuple(vec![])
        }
        FnPtr(_) => MlT::TConstructor(QName::from_string("opaque_ptr").unwrap()),
        // Foreign(_) => todo!(),
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

pub(crate) fn translate_projection_ty<'tcx, C: Cloner<'tcx>>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut C,
    pty: &ProjectionTy<'tcx>,
) -> MlT {
    // ctx.translate(pty.trait_def_id(ctx.tcx));
    let name = names.ty(pty.item_def_id, pty.substs);
    MlT::TConstructor(name)
}

pub(crate) fn intty_to_ty(ity: &creusot_rustc::middle::ty::IntTy) -> MlT {
    use creusot_rustc::middle::ty::IntTy::*;

    match ity {
        Isize => isize_ty(),
        I8 => i8_ty(),
        I16 => i16_ty(),
        I32 => i32_ty(),
        I64 => i64_ty(),
        I128 => i128_ty(),
    }
}

pub(crate) fn uintty_to_ty(ity: &creusot_rustc::middle::ty::UintTy) -> MlT {
    use creusot_rustc::middle::ty::UintTy::*;

    match ity {
        Usize => usize_ty(),
        U8 => u8_ty(),
        U16 => u16_ty(),
        U32 => u32_ty(),
        U64 => u64_ty(),
        U128 => u128_ty(),
    }
}

pub(crate) fn floatty_to_ty(fty: &creusot_rustc::middle::ty::FloatTy) -> MlT {
    use creusot_rustc::middle::ty::FloatTy::*;

    match fty {
        F32 => single_ty(),
        F64 => double_ty(),
    }
}

pub(crate) fn double_ty() -> MlT {
    MlT::TConstructor(QName::from_string("Float64.t").unwrap())
}

pub(crate) fn single_ty() -> MlT {
    MlT::TConstructor(QName::from_string("Float32.t").unwrap())
}

pub(crate) fn u8_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint8").unwrap())
}

pub(crate) fn u16_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint16").unwrap())
}

pub(crate) fn u32_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint32").unwrap())
}

pub(crate) fn u64_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint64").unwrap())
}

pub(crate) fn u128_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint128").unwrap())
}

pub(crate) fn usize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("usize").unwrap())
}

pub(crate) fn i8_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int8").unwrap())
}

pub(crate) fn i16_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int16").unwrap())
}

pub(crate) fn i32_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int32").unwrap())
}

pub(crate) fn i64_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int64").unwrap())
}

pub(crate) fn i128_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int128").unwrap())
}

pub(crate) fn isize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("isize").unwrap())
}
