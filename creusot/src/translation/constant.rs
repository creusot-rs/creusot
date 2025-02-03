use crate::{
    contracts_items::get_builtin,
    ctx::TranslationCtx,
    fmir::{self, Operand},
    traits::TraitResolved,
    translation::pearlite::Literal,
};
use rustc_middle::{
    mir::{self, interpret::AllocRange, ConstValue, UnevaluatedConst},
    ty::{Const, ConstKind, ParamEnv, Ty, TyCtxt},
};
use rustc_span::Span;
use rustc_target::abi::Size;

use super::pearlite::{Term, TermKind};

pub(crate) fn from_mir_constant<'tcx>(
    env: ParamEnv<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    c: &rustc_middle::mir::ConstOperand<'tcx>,
) -> fmir::Operand<'tcx> {
    from_mir_constant_kind(ctx, c.const_, env, c.span)
}

fn from_mir_constant_kind<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    ck: mir::Const<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> fmir::Operand<'tcx> {
    if let mir::Const::Ty(ty, c) = ck {
        return Operand::Constant(from_ty_const(ctx, c, ty, env, span));
    }

    if ck.ty().is_unit() {
        return Operand::Constant(Term {
            kind: TermKind::Tuple { fields: Vec::new() },
            ty: ck.ty(),
            span,
        });
    }
    //
    // let ck = ck.normalize(ctx.tcx, env);

    if ck.ty().peel_refs().is_str() {
        if let mir::Const::Val(ConstValue::Slice { data, meta }, _) = ck {
            let start = Size::from_bytes(0);
            let size = Size::from_bytes(meta);
            let bytes = data
                .inner()
                .get_bytes_strip_provenance(&ctx.tcx, AllocRange { start, size })
                .unwrap();
            let string = std::str::from_utf8(bytes).unwrap();

            return Operand::Constant(Term {
                kind: TermKind::Lit(Literal::String(string.into())),
                ty: ck.ty(),
                span,
            });
        }
    }

    if let mir::Const::Unevaluated(UnevaluatedConst { promoted: Some(p), .. }, _) = ck {
        return Operand::Promoted(p, ck.ty());
    }

    Operand::Constant(Term {
        kind: TermKind::Lit(try_to_bits(ctx, env, ck.ty(), span, ck)),
        ty: ck.ty(),
        span,
    })
}

pub(crate) fn from_ty_const<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    c: Const<'tcx>,
    ty: Ty<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> Term<'tcx> {
    // Check if a constant is builtin and thus should not be evaluated further
    // Builtin constants are given a body which panics
    if let ConstKind::Unevaluated(u) = c.kind()
        && let Some(_) = get_builtin(ctx.tcx, u.def)
    {
        return Term { kind: TermKind::Lit(Literal::Function(u.def, u.args)), ty, span };
    };

    if let ConstKind::Param(_) = c.kind() {
        ctx.crash_and_error(span, "const generic parameters are not yet supported");
    }

    return Term { kind: TermKind::Lit(try_to_bits(ctx, env, ty, span, c)), ty: ty, span };
}

fn try_to_bits<'tcx, C: ToBits<'tcx> + std::fmt::Debug>(
    ctx: &TranslationCtx<'tcx>,
    // names: &mut CloneMap<'tcx>,
    env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
    c: C,
) -> Literal<'tcx> {
    use rustc_middle::ty::{FloatTy, IntTy, UintTy};
    use rustc_type_ir::TyKind::{Bool, Float, FnDef, Int, Uint};
    let Some(bits) = c.get_bits(ctx.tcx, env, ty) else {
        ctx.fatal_error(span, &format!("Could not determine value of constant. Creusot currently does not support generic associated constants.")).emit()
    };

    let target_width = ctx.tcx.sess.target.pointer_width;

    match ty.kind() {
        Int(ity) => {
            let bits: i128 = match ity.normalize(target_width) {
                IntTy::I128 => bits as i128,
                IntTy::Isize => unreachable!("IntTy::Isize for Literal"),  
                IntTy::I8 => bits as i8 as i128,
                IntTy::I16 => bits as i16 as i128,
                IntTy::I32 => bits as i32 as i128,
                IntTy::I64 => bits as i64 as i128,
            };

            Literal::MachSigned(bits, *ity)
        }
        Uint(uty) => {
            let bits: u128 = match uty.normalize(target_width) {
                UintTy::U128 => bits as u128,
                UintTy::Usize => unreachable!("UintTy::Usize for Literal"),  
                UintTy::U8 => bits as u8 as u128,
                UintTy::U16 => bits as u16 as u128,
                UintTy::U32 => bits as u32 as u128,
                UintTy::U64 => bits as u64 as u128,
            };
            Literal::MachUnsigned(bits, *uty)
        }
        Bool => Literal::Bool(bits == 1),
        Float(FloatTy::F32) => {
            let float = f32::from_bits(bits as u32);
            if float.is_nan() {
                ctx.crash_and_error(span, "NaN is not yet supported")
            } else {
                Literal::Float((float as f64).into(), FloatTy::F32)
            }
        }
        Float(FloatTy::F64) => {
            let float = f64::from_bits(bits as u64);
            if float.is_nan() {
                ctx.crash_and_error(span, "NaN is not yet supported")
            } else {
                Literal::Float(float.into(), FloatTy::F64)
            }
        }
        _ if ty.is_unit() => Literal::ZST,
        FnDef(def_id, subst) => {
            let method = TraitResolved::resolve_item(ctx.tcx, env, *def_id, subst)
                .to_opt(*def_id, subst)
                .unwrap();
            Literal::Function(method.0, method.1)
        }
        _ => {
            ctx.crash_and_error(span, &format!("unsupported constant expression"));
        }
    }
}

trait ToBits<'tcx> {
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: ParamEnv<'tcx>, ty: Ty<'tcx>) -> Option<u128>;
}

impl<'tcx> ToBits<'tcx> for Const<'tcx> {
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: ParamEnv<'tcx>, _: Ty<'tcx>) -> Option<u128> {
        self.try_eval_bits(tcx, env)
    }
}
impl<'tcx> ToBits<'tcx> for mir::Const<'tcx> {
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: ParamEnv<'tcx>, _: Ty<'tcx>) -> Option<u128> {
        self.try_eval_bits(tcx, env)
    }
}
