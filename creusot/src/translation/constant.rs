use crate::{
    contracts_items::get_builtin,
    ctx::{HasTyCtxt as _, TranslationCtx},
    translation::{fmir::Operand, pearlite::Literal, traits::TraitResolved},
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{self, interpret::AllocRange, ConstOperand, ConstValue, UnevaluatedConst},
    ty::{self, Const, ConstKind, Ty, TyCtxt, TypingEnv},
};
use rustc_span::{DUMMY_SP, Span};
use rustc_target::abi::Size;

use super::pearlite::{Term, TermKind};

pub(crate) fn from_mir_constant<'tcx>(
    env: TypingEnv<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    c: &ConstOperand<'tcx>,
) -> Operand<'tcx> {
    use mir::Const::*;
    match c.const_ {
        Ty(ty, _) => todo!(),
        Unevaluated(u, ty) if let Some(promoted) = u.promoted => Operand::Promoted(promoted, ty),
        Unevaluated(u, ty) => Operand::AnonConst(u.def, u.args, ty),
        Val(const_value, ty) => Operand::Constant(value_to_term(ctx, const_value, ty, env, c.span)),
    }
}

fn value_to_term<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    value: ConstValue<'tcx>,
    ty: Ty<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Term<'tcx> {
    use ConstValue::*;
    use mir::interpret::Scalar;
    let kind = match value {
        Scalar(Scalar::Int(scalar)) => TermKind::Lit(scalar_to_literal(ctx, env, span, ty, scalar)),
        ZeroSized => TermKind::Lit(Literal::ZST),
        Slice { data, meta } if ty.peel_refs().is_str() => {
            let start = Size::from_bytes(0);
            let size = Size::from_bytes(meta);
            let bytes = data
                .inner()
                .get_bytes_strip_provenance(&ctx.tcx, AllocRange { start, size })
                .unwrap();
            let string = std::str::from_utf8(bytes).unwrap();
            TermKind::Lit(Literal::String(string.into()))
        }
        _ => unimplemented!("{value:?}"),
    };
    Term { kind, ty, span }
}

fn scalar_to_literal<'tcx>(ctx: &TranslationCtx<'tcx>, env: TypingEnv<'tcx>, span: Span, ty: Ty<'tcx>, scalar: ty::ScalarInt) -> Literal<'tcx> {
    try_scalar_to_literal(ctx, env, span, ty, scalar).unwrap_or_else(|| {
        ctx.crash_and_error(span, &format!("Could not convert scalar to literal for type: {:?}", ty))
    })
}

fn try_scalar_to_literal<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
    scalar: ty::ScalarInt,
) -> Option<Literal<'tcx>> {
    use rustc_middle::ty::FloatTy;
    use rustc_type_ir::TyKind::{Bool, Char, Float, Int, Uint};
    let target_width = ctx.tcx.sess.target.pointer_width;
    Some(match ty.kind() {
        Char => Literal::Char(char::try_from(scalar).ok()?),
        Int(ity) => {
            let size = Size::from_bits(ity.normalize(target_width).bit_width().unwrap());
            let bits = size.sign_extend(scalar.try_to_bits(size).ok()?);
            Literal::MachSigned(bits, *ity)
        }
        Uint(uty) => {
            let size = Size::from_bits(uty.normalize(target_width).bit_width().unwrap());
            let bits = scalar.try_to_bits(size).ok()?;
            Literal::MachUnsigned(bits, *uty)
        }
        Bool => Literal::Bool(scalar.try_to_bool().unwrap_or_else(|_| ctx.crash_and_error(span, &format!("can't convert {scalar:?} to bool")))),
        Float(FloatTy::F32) => {
            let float = f32::from_bits(scalar.try_to_bits(Size::from_bits(32)).ok()? as u32);
            if float.is_nan() {
                ctx.crash_and_error(span, "NaN is not yet supported")
            } else {
                Literal::Float((float as f64).into(), FloatTy::F32)
            }
        }
        Float(FloatTy::F64) => {
            let float = f64::from_bits(scalar.try_to_bits(Size::from_bits(64)).ok()? as u64);
            if float.is_nan() {
                ctx.crash_and_error(span, "NaN is not yet supported")
            } else {
                Literal::Float(float.into(), FloatTy::F64)
            }
        }
        _ => ctx.crash_and_error(span, &format!("unsupported constant expression for type: {:?}", ty)),
    })
}

/*
fn from_mir_constant_kind<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    ck: mir::Const<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Operand<'tcx> {
    if let mir::Const::Ty(ty, c) = ck {
        return Operand::Constant(from_ty_const(ctx, c, ty, env, span));
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

    Operand::Constant(Term {
        kind: TermKind::Lit(try_to_bits(ctx, env, ck.ty(), span, ck)),
        ty: ck.ty(),
        span,
    })
}
 */

pub(crate) fn try_from_ty_const<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    c: Const<'tcx>,
    body_id: DefId,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Option<Term<'tcx>> {
    use rustc_type_ir::ConstKind::*;
    match c.kind() {
        Value(ty, value) => valtree_to_term(ctx, value, ty, env, span),
        Param(p) => {
            let def_id = ctx.generics_of(body_id).const_param(p, ctx.tcx).def_id;
            Some(Term {
                kind: TermKind::Lit(Literal::String(format!("{def_id:?}"))),
                ty: p.find_ty_from_env(env.param_env),
                span
            })
        }
        _ => None,
    }
}

pub(crate) fn const_to_term<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    c: Const<'tcx>,
    body_id: DefId,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Term<'tcx> {
    try_from_ty_const(ctx, c, body_id, env, span).unwrap_or_else(|| {
        ctx.crash_and_error(span, &format!("Unsupported constant expression: {c:?}"))
    })
}

fn valtree_to_term<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    valtree: ty::ValTree<'tcx>,
    ty: Ty<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Option<Term<'tcx>> {
    use ty::ValTree::*;
    let kind = match valtree {
        Leaf(scalar) => TermKind::Lit(scalar_to_literal(ctx, env, span, ty, scalar)),
        Branch(_) => {
            let ty::DestructuredConst { variant, fields } = ctx.destructure_const(ty::Const::new_value(ctx.tcx, valtree, ty));
            let fields = fields.into_iter().map(|field| {
                let ty::ConstKind::Value(ty, val) = field.kind() else { unreachable!() };
                valtree_to_term(ctx, val, ty, env, span)
            }).collect::<Option<Box<[_]>>>()?;
            match ty.kind() {
                ty::TyKind::Tuple(_) => TermKind::Tuple { fields },
                ty::TyKind::Adt(__, _) => TermKind::Constructor { variant: variant.unwrap(), fields },
                _ => return None,
            }
        }
    };
    Some(Term { kind, ty, span })
}

fn try_to_bits<'tcx, C: ToBits<'tcx> + std::fmt::Debug>(
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
    c: C,
) -> Literal<'tcx> {
    use rustc_middle::ty::{FloatTy, IntTy, UintTy};
    use rustc_type_ir::TyKind::{Bool, Char, Float, FnDef, Int, Uint};
    let Some(bits) = c.get_bits(ctx.tcx, env, ty) else {
        ctx.fatal_error(span, &format!("Could not determine value of constant. Creusot currently does not support generic associated constants.")).emit()
    };

    let target_width = ctx.tcx.sess.target.pointer_width;

    match ty.kind() {
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
    }
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

/// Translate the body of a logic constant.
/// - `None` if there is no body or the constant can't be represented as a term.
/// - `Some`
pub fn logic_const<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body_id: DefId,
    def_id: DefId,
    subst: ty::GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    if ctx.def_kind(def_id) == DefKind::ConstParam {
        return None;
    }
    let ty = ctx.type_of(def_id).instantiate(ctx.tcx, subst);
    let ty = ctx.tcx.normalize_erasing_regions(typing_env, ty);
    let span = ctx.def_span(def_id);
    let uneval = ty::UnevaluatedConst::new(def_id, subst);
    match ctx.const_eval_resolve_for_typeck(typing_env, uneval, span) {
        Ok(Ok(val)) => valtree_to_term(ctx, val, ty, typing_env, span),
        _ => try_const_synonym(ctx, typing_env, body_id, def_id, subst), // .or_else(|| {
            // let constant = Const::new(ctx.tcx, ty::ConstKind::Unevaluated(uneval));
            // ctx.crash_and_error(span, &format!("unsupported const {constant:?}"))
        // }),
    }
}

/// Handle associated const definitions of the form `const N = M;` where `M` is another constant.
pub(crate) fn try_const_synonym<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body_id: DefId,
    def_id: DefId,
    subst: ty::GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    if !matches!(ctx.def_kind(def_id), rustc_hir::def::DefKind::AssocConst) {
        return None;
    }
    let ty::Instance { def, args } =
        ty::Instance::try_resolve(ctx.tcx, typing_env, def_id, subst).ok()??;
    let body = ctx.instance_mir(def);
    let (c, ty) = body_const(body)?;
    match c {
        ConstKind::Param(p) => {
            let c = args.const_at(p.index as usize);
            Some(const_to_term(ctx, c, body_id, typing_env, DUMMY_SP))
        }
        ConstKind::Unevaluated(u) => {
            let (u, ty) = ty::EarlyBinder::bind((u, ty)).instantiate(ctx.tcx, args);
            Some(Term { kind: TermKind::Item(u.def, u.args), ty, span: DUMMY_SP })
        }
        _ => None,
    }
}

/// Extract constant from MIR body. It should be a single assignment `_0 = const M`.
/// Otherwise return `None`.
fn body_const<'tcx>(body: &mir::Body<'tcx>) -> Option<(ConstKind<'tcx>, Ty<'tcx>)> {
    if body.basic_blocks.len() != 1 {
        return None;
    }
    let block = &body.basic_blocks[mir::BasicBlock::from_usize(0)];
    if block.statements.len() != 1 {
        return None;
    }
    let mir::StatementKind::Assign(box (lhs, rhs)) = &block.statements[0].kind else { return None };
    if lhs.local != mir::Local::from_u32(0) || lhs.projection.len() != 0 {
        return None;
    }
    let mir::Rvalue::Use(mir::Operand::Constant(rhs)) = rhs else { return None };
    match rhs.const_ {
        mir::Const::Ty(ty, c) => Some((c.kind(), ty)),
        mir::Const::Unevaluated(u, ty) => {
            Some((rustc_type_ir::ConstKind::Unevaluated(u.shrink()), ty))
        }
        k => panic!("{k:?}"),
    }
}