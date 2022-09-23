use crate::{
    clone_map::{CloneLevel, CloneMap},
    ctx::{module_name, CloneSummary, TranslationCtx},
    traits::resolve_assoc_item_opt,
    translation::specification::typing::Literal,
    util::get_builtin,
};
use creusot_rustc::{
    hir::def_id::DefId,
    middle::{
        mir::interpret::{AllocRange, ConstValue},
        ty::{Const, ConstKind, ParamEnv, Ty, TyCtxt, Unevaluated},
    },
    smir::mir::ConstantKind,
    span::Span,
    target::abi::Size,
};
use why3::{
    declaration::Module,
    exp::{Constant, Exp},
    QName,
};

use super::fmir::Expr;

impl<'tcx> TranslationCtx<'_, 'tcx> {
    pub fn translate_constant(&mut self, def_id: DefId) -> (Module, CloneSummary<'tcx>) {
        let modl = Module { name: module_name(self, def_id), decls: Vec::new() };

        (modl, CloneSummary::new())
    }
}

pub fn from_mir_constant<'tcx>(
    env: ParamEnv<'tcx>,
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    c: &creusot_rustc::smir::mir::Constant<'tcx>,
) -> Expr<'tcx> {
    from_mir_constant_kind(ctx, names, c.literal, env, c.span)
}

pub fn from_mir_constant_kind<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    ck: creusot_rustc::smir::mir::ConstantKind<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> Expr<'tcx> {
    if let Some(c) = ck.const_for_ty() {
        return from_ty_const(ctx, names, c, env, span);
    }

    if ck.ty().is_unit() {
        return Expr::Tuple(Vec::new());
    }

    if ck.ty().peel_refs().is_str() {
        if let Some(ConstValue::Slice { data, start, end }) = ck.try_to_value(ctx.tcx) {
            let start = Size::from_bytes(start);
            let size = Size::from_bytes(end);
            let bytes = data.inner().get_bytes(&ctx.tcx, AllocRange { start, size }).unwrap();
            let string = std::str::from_utf8(bytes).unwrap();
            return Expr::Exp(Exp::Const(Constant::String(string.into())));
        }
    }

    return Expr::Constant(try_to_bits(ctx, names, env, ck.ty(), span, ck));
}

pub fn from_ty_const<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    c: Const<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> Expr<'tcx> {
    // Check if a constant is builtin and thus should not be evaluated further
    // Builtin constants are given a body which panics
    if let ConstKind::Unevaluated(u) = c.kind() &&
       let Some(builtin_nm) = get_builtin(ctx.tcx, u.def.did) &&
       let Some(nm) = QName::from_string(builtin_nm.as_str()) {
            names.import_builtin_module(nm.clone().module_qname());
            return Expr::Exp(Exp::pure_qvar(nm.without_search_path()));
    };

    if let ConstKind::Unevaluated(Unevaluated { promoted: Some(p), .. }) = c.kind() {
        return Expr::Exp(Exp::impure_var(format!("promoted{:?}", p.as_usize()).into()));
    }

    if let ConstKind::Param(_) = c.kind() {
        ctx.crash_and_error(span, "const generic parameters are not yet supported");
    }

    return Expr::Constant(try_to_bits(ctx, names, env, c.ty(), span, c));
}

fn try_to_bits<'tcx, C: ToBits<'tcx>>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
    c: C,
) -> Literal {
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
            Literal::Int(bits, *ity)
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
            Literal::Uint(bits, *uty)
        }
        Bool => Literal::Bool(c.get_bits(ctx.tcx, env, ty) == Some(1)),
        Float(FloatTy::F32) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            let float = f32::from_bits(bits.unwrap() as u32);
            if float.is_nan() {
                ctx.crash_and_error(span, "NaN is not yet supported")
            } else {
                Literal::Float(float as f64)
            }
        }
        Float(FloatTy::F64) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            let float = f64::from_bits(bits.unwrap() as u64);
            if float.is_nan() {
                ctx.crash_and_error(span, "NaN is not yet supported")
            } else {
                Literal::Float(float)
            }
        }
        _ if ty.is_unit() => Literal::ZST,
        FnDef(def_id, subst) => {
            let method =
                resolve_assoc_item_opt(ctx.tcx, env, *def_id, subst).unwrap_or((*def_id, subst));
            names.insert(method.0, method.1);
            Literal::Function
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
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: ParamEnv<'tcx>, ty: Ty<'tcx>) -> Option<u128> {
        self.try_eval_bits(tcx, env, ty)
    }
}
impl<'tcx> ToBits<'tcx> for ConstantKind<'tcx> {
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: ParamEnv<'tcx>, ty: Ty<'tcx>) -> Option<u128> {
        self.try_eval_bits(tcx, env, ty)
    }
}
