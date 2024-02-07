use crate::{
    ctx::TranslationCtx, traits::resolve_assoc_item_opt, translation::pearlite::Literal,
    util::get_builtin,
};
use rustc_middle::{
    mir::{self, interpret::AllocRange, ConstValue, UnevaluatedConst},
    ty::{Const, ConstKind, ParamEnv, Ty, TyCtxt},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::Size;

use super::{
    fmir::{Expr, ExprKind},
    pearlite::{Term, TermKind},
};

pub(crate) fn from_mir_constant<'tcx>(
    env: ParamEnv<'tcx>,
    ctx: &mut TranslationCtx<'tcx>,
    c: &rustc_middle::mir::ConstOperand<'tcx>,
) -> Expr<'tcx> {
    from_mir_constant_kind(ctx, c.const_, env, c.span)
}

pub(crate) fn from_mir_constant_kind<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    ck: mir::Const<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> Expr<'tcx> {
    if let mir::Const::Ty(c) = ck {
        return from_ty_const(ctx, c, env, span);
    }

    if ck.ty().is_unit() {
        return Expr { kind: ExprKind::Tuple(Vec::new()), ty: ck.ty(), span };
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

            return Expr {
                ty: ck.ty(),
                span,
                kind: ExprKind::Constant(Term {
                    kind: TermKind::Lit(Literal::String(string.into())),
                    ty: ck.ty(),
                    span,
                }),
            };
        }
    }

    if let mir::Const::Unevaluated(UnevaluatedConst { promoted: Some(p), .. }, _) = ck {
        return Expr {
            kind: ExprKind::Constant(Term {
                kind: TermKind::Var(Symbol::intern(&format!("promoted{:?}", p.as_usize()))),
                ty: ck.ty(),
                span,
            }),
            ty: ck.ty(),
            span,
        };
    }

    return Expr {
        kind: ExprKind::Constant(Term {
            kind: TermKind::Lit(try_to_bits(ctx, env, ck.ty(), span, ck)),
            ty: ck.ty(),
            span,
        }),
        ty: ck.ty(),
        span,
    };
}

pub(crate) fn from_ty_const<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    c: Const<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> Expr<'tcx> {
    // Check if a constant is builtin and thus should not be evaluated further
    // Builtin constants are given a body which panics
    if let ConstKind::Unevaluated(u) = c.kind() &&
       let Some(_) = get_builtin(ctx.tcx, u.def) {
            return Expr { kind: ExprKind::Constant(Term { kind: TermKind::Lit(Literal::Function(u.def, u.args)), ty: c.ty(), span}), ty: c.ty(), span }
    };

    if let ConstKind::Param(_) = c.kind() {
        ctx.crash_and_error(span, "const generic parameters are not yet supported");
    }

    return Expr {
        kind: ExprKind::Constant(Term {
            kind: TermKind::Lit(try_to_bits(ctx, env, c.ty(), span, c)),
            ty: c.ty(),
            span,
        }),
        ty: c.ty(),
        span,
    };
}

fn try_to_bits<'tcx, C: ToBits<'tcx>>(
    ctx: &mut TranslationCtx<'tcx>,
    // names: &mut CloneMap<'tcx>,
    env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
    c: C,
) -> Literal<'tcx> {
    use rustc_middle::ty::{FloatTy, IntTy, UintTy};
    use rustc_type_ir::sty::TyKind::{Bool, Float, FnDef, Int, Uint};
    match ty.kind() {
        Int(ity) => {
            let bits = c.get_bits(ctx.tcx, env, ty).unwrap();
            let bits: i128 = match *ity {
                IntTy::I128 => bits as i128,
                IntTy::Isize => bits as i64 as i128,
                IntTy::I8 => bits as i8 as i128,
                IntTy::I16 => bits as i16 as i128,
                IntTy::I32 => bits as i32 as i128,
                IntTy::I64 => bits as i64 as i128,
            };
            Literal::MachSigned(bits, *ity)
        }
        Uint(uty) => {
            let bits = c.get_bits(ctx.tcx, env, ty).unwrap();
            let bits: u128 = match *uty {
                UintTy::U128 => bits as u128,
                UintTy::Usize => bits as u64 as u128,
                UintTy::U8 => bits as u8 as u128,
                UintTy::U16 => bits as u16 as u128,
                UintTy::U32 => bits as u32 as u128,
                UintTy::U64 => bits as u64 as u128,
            };
            Literal::MachUnsigned(bits, *uty)
        }
        Bool => Literal::Bool(c.get_bits(ctx.tcx, env, ty) == Some(1)),
        Float(FloatTy::F32) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            let float = f32::from_bits(bits.unwrap() as u32);
            if float.is_nan() {
                ctx.crash_and_error(span, "NaN is not yet supported")
            } else {
                Literal::Float((float as f64).into(), FloatTy::F32)
            }
        }
        Float(FloatTy::F64) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            let float = f64::from_bits(bits.unwrap() as u64);
            if float.is_nan() {
                ctx.crash_and_error(span, "NaN is not yet supported")
            } else {
                Literal::Float(float.into(), FloatTy::F64)
            }
        }
        _ if ty.is_unit() => Literal::ZST,
        FnDef(def_id, subst) => {
            let method =
                resolve_assoc_item_opt(ctx.tcx, env, *def_id, subst).unwrap_or((*def_id, subst));
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
