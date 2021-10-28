use rustc_hir::def_id::DefId;
use rustc_span::Span;
use why3::mlcfg::{self, Constant, Exp};

use crate::{clone_map::CloneMap, ctx::TranslationCtx, translation::ty};

pub fn from_mir_constant<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    _id: DefId,
    c: &rustc_middle::mir::Constant<'tcx>,
) -> mlcfg::Exp {
    from_mir_constant_kind(ctx, names, c.literal, _id, c.span)
}

pub fn from_mir_constant_kind<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    ck: rustc_middle::mir::ConstantKind<'tcx>,
    _id: DefId,
    span: Span,
) -> mlcfg::Exp {
    use rustc_middle::ty::TyKind::{Bool, Int, Uint};
    use rustc_middle::ty::{IntTy::*, UintTy::*};
    use rustc_target::abi::Size;

    // use rustc_middle::ty::consts::*;
    let ty = ty::translate_ty(ctx, names, span, ck.ty());
    match ck.ty().kind() {
        Int(I8) => Exp::Const(Constant::Int(
            ck.try_to_bits(Size::from_bytes(1)).unwrap() as i128,
            Some(ty),
        )),
        Int(I16) => Exp::Const(Constant::Int(
            ck.try_to_bits(Size::from_bytes(2)).unwrap() as i128,
            Some(ty),
        )),
        Int(I32) => Exp::Const(Constant::Int(
            ck.try_to_bits(Size::from_bytes(4)).unwrap() as i128,
            Some(ty),
        )),
        Int(I64) => Exp::Const(Constant::Int(
            ck.try_to_bits(Size::from_bytes(8)).unwrap() as i128,
            Some(ty),
        )),
        Int(I128) => unimplemented!("128-bit integers are not supported"),

        Uint(U8) => {
            Exp::Const(Constant::Uint(ck.try_to_bits(Size::from_bytes(1)).unwrap(), Some(ty)))
        }
        Uint(U16) => {
            Exp::Const(Constant::Uint(ck.try_to_bits(Size::from_bytes(2)).unwrap(), Some(ty)))
        }
        Uint(U32) => {
            Exp::Const(Constant::Uint(ck.try_to_bits(Size::from_bytes(4)).unwrap(), Some(ty)))
        }
        Uint(U64) => {
            Exp::Const(Constant::Uint(ck.try_to_bits(Size::from_bytes(8)).unwrap(), Some(ty)))
        }
        Uint(U128) => {
            unimplemented!("128-bit integers are not supported")
        }
        Uint(Usize) => {
            Exp::Const(Constant::Uint(ck.try_to_bits(Size::from_bytes(8)).unwrap(), Some(ty)))
        }
        Bool => {
            if ck.try_to_bool().unwrap() {
                Exp::mk_true()
            } else {
                Exp::mk_false()
            }
        }
        _ if ck.ty().is_unit() => {
            Exp::Tuple(Vec::new())
        }
        _ => {
            ctx.crash_and_error(
                span,
                &format!("unsupported constant expression, try binding this to a variable. See issue #163 {:?}", ck),
            );
        }
    }
}
