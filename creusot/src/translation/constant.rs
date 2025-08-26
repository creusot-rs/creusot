use crate::{
    ctx::{HasTyCtxt as _, TranslationCtx},
    translation::{fmir::Operand, pearlite::Literal, traits},
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{self, ConstOperand, ConstValue, TerminatorKind, interpret::AllocRange},
    ty::{self, Const, ConstKind, Ty, TypingEnv},
};
use rustc_span::Span;
use rustc_target::abi::Size;

use super::pearlite::{Term, TermKind};

/// Translate constant MIR operands
pub(crate) fn mirconst_to_operand<'tcx>(
    c: &ConstOperand<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    caller_id: DefId,
) -> Operand<'tcx> {
    use mir::Const::*;
    match c.const_ {
        Ty(_ty, tyconst) => Operand::Term(tyconst_to_term(tyconst, ctx, env, caller_id, c.span)),
        Unevaluated(u, ty) if let Some(promoted) = u.promoted => {
            Operand::promoted(caller_id, promoted, ty)
        }
        Unevaluated(u, ty) if matches!(ctx.def_kind(u.def), DefKind::InlineConst) => {
            Operand::inline_const(u.def, u.args, ty)
        }
        Unevaluated(u, ty) => Operand::Term(Term::item(u.def, u.args, ty, c.span)),
        Val(const_value, ty) => Operand::Term(value_to_term(const_value, ty, ctx, env, c.span)),
    }
}

fn value_to_term<'tcx>(
    value: ConstValue<'tcx>,
    ty: Ty<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Term<'tcx> {
    use ConstValue::*;
    use mir::interpret::Scalar;
    let kind = match value {
        Scalar(Scalar::Int(scalar)) => TermKind::Lit(scalar_to_literal(scalar, ty, ctx, env, span)),
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
        _ => ctx
            .crash_and_error(span, format!("Unsupported constant value: {value:?} of type {ty:?}")),
    };
    Term { kind, ty, span }
}

fn scalar_to_literal<'tcx>(
    scalar: ty::ScalarInt,
    ty: Ty<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Literal<'tcx> {
    try_scalar_to_literal(scalar, ty, ctx, env, span).unwrap_or_else(|| {
        ctx.crash_and_error(span, format!("Could not convert scalar to literal for type: {:?}", ty))
    })
}

fn try_scalar_to_literal<'tcx>(
    scalar: ty::ScalarInt,
    ty: Ty<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Option<Literal<'tcx>> {
    use rustc_middle::ty::FloatTy;
    use rustc_type_ir::TyKind::*;
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
        Bool => Literal::Bool(scalar.try_to_bool().unwrap_or_else(|_| {
            ctx.crash_and_error(span, format!("can't convert {scalar:?} to bool"))
        })),
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
        FnDef(def_id, subst) => {
            let method = traits::resolve_item(ctx.tcx, env, *def_id, subst).expect_found(span);
            Literal::Function(method.0, method.1)
        }
        kind => ctx.crash_and_error(span, format!("unsupported constant expression {kind:?}")),
    })
}

// This is also used in the translation of `RValue::Repeat`.
pub(crate) fn tyconst_to_term<'tcx>(
    c: Const<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    caller_id: DefId,
    span: Span,
) -> Term<'tcx> {
    try_tyconst_to_term(c, ctx, env, caller_id, span).unwrap_or_else(|| {
        ctx.crash_and_error(span, format!("Unsupported constant expression: {c:?}"))
    })
}

fn try_tyconst_to_term<'tcx>(
    c: Const<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    caller_id: DefId,
    span: Span,
) -> Option<Term<'tcx>> {
    use rustc_type_ir::ConstKind::*;
    match c.kind() {
        Value(ty, value) => valtree_to_term(value, ctx, ty, env, span),
        Param(p) => {
            let def_id = ctx.generics_of(caller_id).const_param(p, ctx.tcx).def_id;
            let ty = ctx.type_of(def_id).instantiate_identity();
            Some(Term::const_param(ctx.tcx, def_id, ty, span))
        }
        _ => None,
    }
}

/// Translate constant with a simple body: it can be reduced to a value expressible in
/// the logical fragment of Why3, or its body is just a variable.
/// `None` if it does not match these cases.
pub fn try_const_to_term<'tcx>(
    def_id: DefId,
    subst: ty::GenericArgsRef<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    caller_id: DefId,
) -> Option<Term<'tcx>> {
    if ctx.def_kind(def_id) == DefKind::ConstParam {
        return None;
    }
    let ty = ctx.type_of(def_id).instantiate(ctx.tcx, subst);
    let ty = ctx.tcx.normalize_erasing_regions(typing_env, ty);
    let span = ctx.def_span(def_id);
    let uneval = ty::UnevaluatedConst::new(def_id, subst);
    match ctx.const_eval_resolve_for_typeck(typing_env, uneval, span) {
        Ok(Ok(val)) => valtree_to_term(val, ctx, ty, typing_env, span),
        _ => try_const_synonym(def_id, subst, ctx, typing_env, caller_id),
    }
}

fn valtree_to_term<'tcx>(
    valtree: ty::ValTree<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    ty: Ty<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
) -> Option<Term<'tcx>> {
    use ty::ValTree::*;
    let kind = match valtree {
        Leaf(scalar) => TermKind::Lit(scalar_to_literal(scalar, ty, ctx, env, span)),
        Branch(_) if matches!(ty.kind(), ty::TyKind::Adt(_, _) | ty::TyKind::Tuple(_)) => {
            let ty::DestructuredConst { variant, fields } =
                ctx.destructure_const(ty::Const::new_value(ctx.tcx, valtree, ty));
            let fields = fields
                .into_iter()
                .map(|field| {
                    let ty::ConstKind::Value(ty, val) = field.kind() else { unreachable!() };
                    valtree_to_term(val, ctx, ty, env, span)
                })
                .collect::<Option<Box<[_]>>>()?;
            match ty.kind() {
                ty::TyKind::Tuple(_) => TermKind::Tuple { fields },
                ty::TyKind::Adt(__, _) => {
                    TermKind::Constructor { variant: variant.unwrap(), fields }
                }
                _ => return None,
            }
        }
        _ => return None,
    };
    Some(Term { kind, ty, span })
}

/// Handle const definitions of the form `const N = M;` where `M` is another constant.
fn try_const_synonym<'tcx>(
    def_id: DefId,
    subst: ty::GenericArgsRef<'tcx>,
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    caller_id: DefId,
) -> Option<Term<'tcx>> {
    if !matches!(ctx.def_kind(def_id), rustc_hir::def::DefKind::AssocConst) {
        return None;
    }
    let ty::Instance { def, args } =
        ty::Instance::try_resolve(ctx.tcx, typing_env, def_id, subst).ok()??;
    let body = ctx.instance_mir(def);
    let (c, ty, span) = simple_body_const(body)?;
    match c {
        ConstKind::Param(p) => {
            let c = args.const_at(p.index as usize);
            Some(tyconst_to_term(c, ctx, typing_env, caller_id, span))
        }
        ConstKind::Unevaluated(u)
            if matches!(ctx.def_kind(u.def), DefKind::Const | DefKind::AssocConst) =>
        {
            let (u, ty) = ty::EarlyBinder::bind((u, ty)).instantiate(ctx.tcx, args);
            Some(Term { kind: TermKind::Item(u.def, u.args), ty, span })
        }
        _ => None,
    }
}

/// Extract constant from MIR body. It should be a single assignment `_0 = const M`.
/// Otherwise return `None`.
fn simple_body_const<'tcx>(body: &mir::Body<'tcx>) -> Option<(ConstKind<'tcx>, Ty<'tcx>, Span)> {
    if body.basic_blocks.len() != 1 {
        return None;
    }
    let block = &body.basic_blocks[mir::BasicBlock::from_usize(0)];
    if block.statements.len() != 1 || !matches!(block.terminator().kind, TerminatorKind::Return) {
        return None;
    }
    let mir::StatementKind::Assign(box (lhs, rhs)) = &block.statements[0].kind else { return None };
    if lhs.local != mir::Local::from_u32(0) || lhs.projection.len() != 0 {
        return None;
    }
    let mir::Rvalue::Use(mir::Operand::Constant(rhs)) = rhs else { return None };
    match rhs.const_ {
        mir::Const::Ty(ty, c) => Some((c.kind(), ty, rhs.span)),
        mir::Const::Unevaluated(u, ty) => {
            Some((rustc_type_ir::ConstKind::Unevaluated(u.shrink()), ty, rhs.span))
        }
        _ => return None,
    }
}
