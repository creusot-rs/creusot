use crate::{
    contracts_items::get_builtin,
    ctx::TranslationCtx, ctx::TranslationCtx,
    translation::{fmir::Operand, pearlite::Literal, traits::TraitResolved},
};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{self, ConstOperand, interpret::AllocRange, ConstValue, UnevaluatedConst, BasicBlock, Statement, StatementKind},
    ty::{Const, ConstKind, AssocItem, AssocItemContainer, EarlyBinder, ScalarInt, Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::{DUMMY_SP, Span};
use rustc_target::abi::Size;

use super::pearlite::{Term, TermKind};

impl<'tcx> super::function::BodyTranslator<'_, 'tcx> {
    pub(crate) fn from_mir_constant(
        &self,
        c: &rustc_middle::mir::ConstOperand<'tcx>,
    ) -> fmir::Operand<'tcx> {
        mir_const_to_operand(self.ctx, self.typing_env(), self.def_id(), c.const_, c.span)
    }

    pub(crate) fn translate_const(
        &self,
        c: ty::Const<'tcx>,
        ty: ty::Ty<'tcx>,
        span: Span,
    ) -> Term<'tcx> {
        const_to_term(self.ctx, self.typing_env(), self.def_id(), c, span)
    }
}

fn mir_const_to_operand<'tcx>(ctx: &TranslationCtx<'tcx>, typing_env: TypingEnv<'tcx>, body_id: DefId, c: mir::Const<'tcx>, span: Span) -> fmir::Operand<'tcx> {
    use mir::Const::*;
    match c {
        Ty(_ty, c) => Operand::Constant(const_to_term(ctx, typing_env, body_id, c, span)),
        Unevaluated(UnevaluatedConst { promoted: Some(p), .. }, ty) => Operand::Promoted(p, ty),
        // Try to get a literal value
        Unevaluated(uneval, ty) => match ctx.const_eval_resolve(typing_env, uneval, span) {
            Ok(val) => Operand::Constant(const_value_to_term(ctx, typing_env, span, val, ty)),
            Err(_) => Operand::ConstBlock(uneval.def, uneval.args, ty),
        },
        Val(val, ty) => Operand::Constant(const_value_to_term(ctx, typing_env, span, val, ty)),
    }
}

pub fn const_eval<'tcx>(ctx: &TranslationCtx<'tcx>, typing_env: TypingEnv<'tcx>, body_id: DefId, ty: Ty<'tcx>, def_id: DefId, args: ty::GenericArgsRef<'tcx>) -> Term<'tcx> {
    let span = ctx.def_span(def_id);
    let uneval = ty::UnevaluatedConst::new(def_id, args);
    match ctx.const_eval_resolve_for_typeck(typing_env, uneval, span) {
        Ok(Ok(val)) => value_to_term(ctx, typing_env, span, ty, val),
        _ => try_const_synonym(ctx, typing_env, body_id, def_id, args).unwrap_or_else(|| {
            let constant = Const::new(ctx.tcx, ConstKind::Unevaluated(uneval));
            ctx.crash_and_error(span, &format!("unsupported const {constant:?}"))
        }),
    }
}

fn value_to_term<'tcx>(ctx: &TranslationCtx<'tcx>, typing_env: TypingEnv<'tcx>, span: Span, ty: Ty<'tcx>, val: ty::ValTree<'tcx>) -> Term<'tcx> {
    if let ty::ValTree::Leaf(scalar) = val {
        return Term { kind: TermKind::Lit(scalar_to_literal(ctx, typing_env, span, ty, scalar)), ty, span }
    }
    let ty::DestructuredConst { variant, fields } = ctx.destructure_const(ty::Const::new_value(ctx.tcx, val, ty));
    let fields = fields.into_iter().map(|field| {
        let ty::ConstKind::Value(ty, val) = field.kind() else { unreachable!() };
        value_to_term(ctx, typing_env, span, ty, val)
    }).collect();
    let kind = match ty.kind() {
        TyKind::Tuple(_) => TermKind::Tuple { fields },
        TyKind::Adt(adt, _) => TermKind::Constructor { typ: adt.did(), variant: variant.unwrap(), fields },
        _ => ctx.crash_and_error(span, &format!("unsupported destructured const {val:?}")),
    };
    Term { kind, ty, span }
}

fn const_value_to_term<'tcx>(ctx: &TranslationCtx<'tcx>, typing_env: TypingEnv<'tcx>, span: Span, val: mir::ConstValue<'tcx>, ty: Ty<'tcx>) -> Term<'tcx> {
    use mir::ConstValue::*;
    use mir::interpret::Scalar;
    match val {
        Scalar(Scalar::Int(scalar)) => Term {
            kind: TermKind::Lit(scalar_to_literal(ctx, typing_env, span, ty, scalar)),
            ty,
            span,
        },
        ZeroSized => Term { kind: TermKind::Lit(Literal::ZST), ty, span },
        Slice { data, meta } if ty.peel_refs().is_str() => {
            let start = Size::from_bytes(0);
            let size = Size::from_bytes(meta);
            let bytes = data.inner().get_bytes_strip_provenance(&ctx.tcx, AllocRange { start, size })
                .unwrap();
            let string = std::str::from_utf8(bytes).unwrap();
            let kind = TermKind::Lit(Literal::String(string.into()));
            Term { kind, ty, span }
        }
        _ => ctx.crash_and_error(span, &format!("unsupported const value {val:?}")),
    }
}

pub fn const_to_term<'tcx>(ctx: &TranslationCtx<'tcx>, typing_env: TypingEnv<'tcx>, body_id: DefId, c: ty::Const<'tcx>, span: Span) -> Term<'tcx> {
    use rustc_type_ir::ConstKind::*;
    match c.kind() {
        Param(p) => {
            let def_id = ctx.generics_of(body_id).const_param(p, ctx.tcx).def_id;
            Term {
                kind: TermKind::ConstParam(def_id),
                ty: p.find_ty_from_env(typing_env.param_env),
                span,
            }
        }
        Infer(_) => todo!(),
        Bound(_, _) => todo!(),
        Placeholder(_) => todo!(),
        Unevaluated(_) => todo!(),
        Value(ty, v) => value_to_term(ctx, typing_env, span, ty, v),
        Error(_) => todo!(),
        Expr(_) => todo!(),
    }
}

/// Handle associated const definitions of the form `const N = M;` where `M` is another constant.
pub(crate) fn try_const_synonym<'tcx>(ctx: &TranslationCtx<'tcx>, typing_env: TypingEnv<'tcx>, body_id: DefId, def_id: DefId, subst: ty::GenericArgsRef<'tcx>) -> Option<Term<'tcx>> {
    if !matches!(ctx.def_kind(def_id), rustc_hir::def::DefKind::AssocConst) {
        return None
    }
    let ty::Instance { def, args } = ty::Instance::try_resolve(ctx.tcx, typing_env, def_id, subst).ok()??;
    let body = ctx.instance_mir(def);
    let (c, ty) = body_const(body)?;
    match c {
        ConstKind::Param(p) => {
            let c = args.const_at(p.index as usize);
            Some(const_to_term(ctx, typing_env, body_id, c, DUMMY_SP))
        }
        ConstKind::Unevaluated(u) => {
            let (u, ty) = EarlyBinder::bind((u, ty)).instantiate(ctx.tcx, args);
            Some(Term {
                kind: TermKind::NamedConst(u.def, u.args),
                ty,
                span: DUMMY_SP,
            })
        }
        _ => None,
    }
}

/// Extract constant from MIR body. It should be a single assignment `_0 = const M`.
/// Otherwise return `None`.
fn body_const<'tcx>(body: &mir::Body<'tcx>) -> Option<(ConstKind<'tcx>, Ty<'tcx>)> {
    if body.basic_blocks.len() != 1 { return None }
    let block = &body.basic_blocks[BasicBlock::from_usize(0)];
    if block.statements.len() != 1 { return None }
    let StatementKind::Assign(box (lhs, rhs)) = &block.statements[0].kind else { return None };
    if lhs.local != mir::Local::from_u32(0) || lhs.projection.len() != 0 { return None }
    let mir::Rvalue::Use(mir::Operand::Constant(rhs)) = rhs else { return None };
    match rhs.const_ {
        mir::Const::Ty(ty, c) => Some((c.kind(), ty)),
        mir::Const::Unevaluated(u, ty) => Some((rustc_type_ir::ConstKind::Unevaluated(u.shrink()), ty)),
        k => panic!("{k:?}"),
    }
}

fn scalar_to_literal<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
    scalar: ty::ScalarInt,
) -> Literal<'tcx> {
    try_scalar_to_literal(ctx, env, span, ty, scalar).unwrap_or_else(||
        ctx.crash_and_error(span, &format!("can't convert {scalar:?} to {ty:?}"))
    )
}

fn try_scalar_to_literal<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
    scalar: ty::ScalarInt,
) -> Option<Literal<'tcx>> {
    use rustc_middle::ty::FloatTy;
    use rustc_type_ir::TyKind::{Bool, Char, Float, FnDef, Int, Uint};
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
        Bool => Literal::Bool(scalar.try_to_bool().unwrap_or_else(|_|  ctx.crash_and_error(span, "can't convert {scalar:?} to bool"))),
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
