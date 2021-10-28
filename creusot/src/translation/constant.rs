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

    let ty = ty::translate_ty(ctx, names, span, ck.ty());
    match ck.ty().kind() {
        Int(I128) => unimplemented!("128-bit integers are not supported"),
        Int(_) => {
            let bits = ck.try_eval_bits(ctx.tcx, ctx.tcx.param_env(_id), ck.ty());
            Exp::Const(Constant::Int(i128::from_be_bytes(bits.unwrap().to_be_bytes()), Some(ty)))
        }
        Uint(U128) => unimplemented!("128-bit integers are not supported"),
        Uint(_) => {
            let bits = ck.try_eval_bits(ctx.tcx, ctx.tcx.param_env(_id), ck.ty());
            Exp::Const(Constant::Uint(bits.unwrap(), Some(ty)))
        }
        Bool => {
            if ck.try_to_bool().unwrap() {
                Exp::mk_true()
            } else {
                Exp::mk_false()
            }
        }
        _ if ck.ty().is_unit() => Exp::Tuple(Vec::new()),
        _ => {
            ctx.crash_and_error(
                span,
                &format!("unsupported constant expression, try binding this to a variable. See issue #163 {:?}", ck),
            );
        }
    }
}
