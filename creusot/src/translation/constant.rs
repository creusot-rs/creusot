use crate::{
    contracts_items::get_builtin,
    ctx::TranslationCtx,
    translation::{fmir::Operand, pearlite::Literal, traits::TraitResolved},
};
use rustc_middle::{
    mir::{self, ConstOperand, ConstValue, UnevaluatedConst, interpret::AllocRange},
    ty::{Const, ConstKind, Ty, TyCtxt, TypingEnv},
};
use rustc_span::{DUMMY_SP, Span};
use rustc_target::abi::Size;

use super::pearlite::{Term, TermKind};

pub(crate) fn from_mir_constant<'tcx>(
    env: TypingEnv<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    c: &ConstOperand<'tcx>,
) -> Operand<'tcx> {
    from_mir_constant_kind(ctx, c.const_, env, c.span)
}

fn from_mir_constant_kind<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    ck: mir::Const<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Operand<'tcx> {
    if let mir::Const::Ty(ty, c) = ck {
        return Operand::Constant(from_ty_const(ctx, c, ty, env, span).expect("unexpected const"));
    }

    if ck.ty().is_unit() {
        return Operand::Constant(Term::unit(ctx.tcx));
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

    if let Some(lit) = try_to_bits(ctx, env, ck.ty(), span, ck) {
        return Operand::Constant(Term { kind: TermKind::Lit(lit), ty: ck.ty(), span });
    }

    const_block(ctx, span, ck)
}

pub(crate) fn from_ty_const<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    c: Const<'tcx>,
    ty: Ty<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Option<Term<'tcx>> {
    // Check if a constant is builtin and thus should not be evaluated further
    // Builtin constants are given a body which panics
    if let ConstKind::Unevaluated(u) = c.kind()
        && get_builtin(ctx.tcx, u.def).is_some()
    {
        return Some(Term { kind: TermKind::Lit(Literal::Function(u.def, u.args)), ty, span });
    };

    if let Some(lit) = try_to_bits(ctx, env, ty, span, c) {
        return Some(Term { kind: TermKind::Lit(lit), ty, span });
    }

    None
}

fn try_to_bits<'tcx, C: ToBits<'tcx> + std::fmt::Debug>(
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
    c: C,
) -> Option<Literal<'tcx>> {
    use rustc_middle::ty::{FloatTy, IntTy, UintTy};
    use rustc_type_ir::TyKind::{Bool, Char, Float, FnDef, Int, Uint};
    let bits = c.get_bits(ctx.tcx, env, ty)?;
    let target_width = ctx.tcx.sess.target.pointer_width;

    Some(match ty.kind() {
        Char => Literal::Char(
            char::from_u32(bits as u32)
                .unwrap_or_else(|| ctx.crash_and_error(span, "can't convert to char")),
        ),
        Int(ity) => {
            let bits: i128 = match ity.normalize(target_width) {
                IntTy::Isize => unreachable!(),
                IntTy::I8 => bits as i8 as i128,
                IntTy::I16 => bits as i16 as i128,
                IntTy::I32 => bits as i32 as i128,
                IntTy::I64 => bits as i64 as i128,
                IntTy::I128 => bits as i128,
            };
            Literal::MachSigned(bits, *ity)
        }
        Uint(uty) => {
            let bits: u128 = match uty.normalize(target_width) {
                UintTy::Usize => unreachable!(),
                UintTy::U8 => bits as u8 as u128,
                UintTy::U16 => bits as u16 as u128,
                UintTy::U32 => bits as u32 as u128,
                UintTy::U64 => bits as u64 as u128,
                UintTy::U128 => bits as u128,
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
    })
}

trait ToBits<'tcx> {
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: TypingEnv<'tcx>, ty: Ty<'tcx>) -> Option<u128>;
}

impl<'tcx> ToBits<'tcx> for Const<'tcx> {
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: TypingEnv<'tcx>, ty: Ty<'tcx>) -> Option<u128> {
        let scalar = match self.kind() {
            ConstKind::Value(_, _) => self.try_to_scalar()?.0,
            ConstKind::Unevaluated(u) => {
                tcx.const_eval_resolve_for_typeck(env, u, DUMMY_SP).ok()?.ok()?.try_to_scalar()?
            }
            _ => return None,
        };
        let input = env.with_post_analysis_normalized(tcx).as_query_input(ty);
        let size = tcx.layout_of(input).ok()?.size;
        Some(scalar.try_to_scalar_int().ok()?.to_bits(size))
    }
}

impl<'tcx> ToBits<'tcx> for mir::Const<'tcx> {
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: TypingEnv<'tcx>, _: Ty<'tcx>) -> Option<u128> {
        self.try_eval_bits(tcx, env)
    }
}

fn const_block<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    span: Span,
    ck: mir::Const<'tcx>,
) -> fmir::Operand<'tcx> {
    match ck {
        mir::Const::Unevaluated(UnevaluatedConst { def, args, .. }, ty) => {
            return Operand::ConstBlock(def, args, ty);
        }
        _ => ctx.crash_and_error(span, "unsupported const {ck}"),
    }
}
