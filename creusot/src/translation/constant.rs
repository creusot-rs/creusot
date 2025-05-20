use crate::{
    contracts_items::get_builtin,
    ctx::TranslationCtx, ctx::TranslationCtx,
    translation::{fmir::Operand, pearlite::Literal, traits::TraitResolved},
};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{self, ConstOperand, interpret::AllocRange, ConstValue, UnevaluatedConst, BasicBlock, Statement, StatementKind},
    ty::{Const, ConstKind, AssocItem, AssocItemContainer, EarlyBinder, Ty, TyCtxt, TypingEnv},
};
use rustc_span::{DUMMY_SP, Span};
use rustc_target::abi::Size;

use super::pearlite::{Term, TermKind};

impl<'tcx> super::function::BodyTranslator<'_, 'tcx> {
    pub(crate) fn from_mir_constant(
        &self,
        c: &rustc_middle::mir::ConstOperand<'tcx>,
    ) -> fmir::Operand<'tcx> {
        let env = self.typing_env();
        let ck = c.const_;
        let span = c.span;
        if let mir::Const::Ty(ty, c) = ck {
            return Operand::Constant(self.translate_const(c, ty, span));
        }

        if ck.ty().is_unit() {
            return Operand::Constant(Term::unit(self.ctx.tcx));
        }
        //
        // let ck = ck.normalize(ctx.tcx, env);

        if ck.ty().peel_refs().is_str() {
            if let mir::Const::Val(ConstValue::Slice { data, meta }, _) = ck {
                let start = Size::from_bytes(0);
                let size = Size::from_bytes(meta);
                let bytes = data
                    .inner()
                    .get_bytes_strip_provenance(&self.ctx.tcx, AllocRange { start, size })
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

        if let Some(lit) = try_to_bits(self.ctx, env, ck.ty(), span, ck) {
            return Operand::Constant(Term { kind: TermKind::Lit(lit), ty: ck.ty(), span });
        }

        const_block(self.ctx, span, ck)
    }

    pub(crate) fn translate_const(
        &self,
        c: ty::Const<'tcx>,
        ty: ty::Ty<'tcx>,
        span: Span,
    ) -> Term<'tcx> {
        if let Some(t) = try_eval_const(self.ctx, self.typing_env(), c, ty, span) {
            return t;
        }
        translate_const(self.ctx, self.typing_env(), self.def_id(), c, span)
    }

}

fn translate_const<'tcx>(ctx: &TranslationCtx<'tcx>, typing_env: TypingEnv<'tcx>, body_id: DefId, c: ty::Const<'tcx>, span: Span) -> Term<'tcx> {
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
        Value(ty, v) => todo!(),
        Error(_) => todo!(),
        Expr(_) => todo!(),
    }
}

/// Try to evaluate a `const` expression to a literal.
pub(crate) fn try_eval_const<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    env: TypingEnv<'tcx>,
    c: Const<'tcx>,
    ty: Ty<'tcx>,
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
            Some(translate_const(ctx, typing_env, body_id, c, DUMMY_SP))
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
