use crate::{
    backend::logic::stub_module,
    clone_map::CloneMap,
    ctx::{module_name, CloneSummary, TranslatedItem, TranslationCtx},
    traits::resolve_assoc_item_opt,
    translation::pearlite::Literal,
    util::{get_builtin, signature_of},
};
use creusot_rustc::{
    hir::def_id::DefId,
    middle::{
        mir::{
            interpret::{AllocRange, ConstValue},
            UnevaluatedConst,
        },
        ty,
        ty::{Const, ConstKind, ParamEnv, Ty, TyCtxt},
    },
    smir::mir::ConstantKind,
    span::{Span, Symbol},
    target::abi::Size,
};
use rustc_middle::ty::subst::InternalSubsts;
use why3::declaration::{Decl, LetDecl, LetKind, Module};

use super::{
    fmir::Expr,
    pearlite::{Term, TermKind},
};

impl<'tcx> TranslationCtx<'tcx> {
    pub(crate) fn translate_constant(
        &mut self,
        def_id: DefId,
    ) -> (TranslatedItem, CloneSummary<'tcx>) {
        let subst = InternalSubsts::identity_for_item(self.tcx, def_id);
        let uneval = ty::UnevaluatedConst::new(ty::WithOptConstParam::unknown(def_id), subst);
        let constant = self.mk_const(ty::ConstS {
            kind: ty::ConstKind::Unevaluated(uneval),
            ty: self.type_of(def_id),
        });

        let res = from_ty_const(self, constant, self.param_env(def_id), self.def_span(def_id));
        let mut names = CloneMap::new(self.tcx, def_id, crate::clone_map::CloneLevel::Body);
        let res = res.to_why(self, &mut names, None);
        let sig = signature_of(self, &mut names, def_id);
        let mut decls = names.to_clones(self);
        decls.push(Decl::Let(LetDecl {
            kind: Some(LetKind::Constant),
            sig: sig.clone(),
            rec: false,
            ghost: false,
            body: res,
        }));

        let stub = stub_module(self, def_id);

        let modl = Module { name: module_name(self, def_id), decls };
        (TranslatedItem::Constant { stub, modl }, CloneSummary::new())
    }
}

pub(crate) fn from_mir_constant<'tcx>(
    env: ParamEnv<'tcx>,
    ctx: &mut TranslationCtx<'tcx>,
    c: &creusot_rustc::smir::mir::Constant<'tcx>,
) -> Expr<'tcx> {
    from_mir_constant_kind(ctx, c.literal, env, c.span)
}

pub(crate) fn from_mir_constant_kind<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    ck: ConstantKind<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> Expr<'tcx> {
    if let ConstantKind::Ty(c) = ck {
        return from_ty_const(ctx, c, env, span);
    }

    if ck.ty().is_unit() {
        return Expr::Tuple(Vec::new());
    }

    if ck.ty().peel_refs().is_str() {
        if let Some(ConstValue::Slice { data, start, end }) = ck.try_to_value(ctx.tcx) {
            let start = Size::from_bytes(start);
            let size = Size::from_bytes(end);
            let bytes = data
                .inner()
                .get_bytes_strip_provenance(&ctx.tcx, AllocRange { start, size })
                .unwrap();
            let string = std::str::from_utf8(bytes).unwrap();

            return Expr::Constant(Term {
                kind: TermKind::Lit(Literal::String(string.into())),
                ty: ck.ty(),
                span,
            });
        }
    }

    if let ConstantKind::Unevaluated(UnevaluatedConst { promoted: Some(p), .. }, _) = ck {
        return Expr::Constant(Term {
            kind: TermKind::Var(Symbol::intern(&format!("promoted{:?}", p.as_usize()))),
            ty: ck.ty(),
            span,
        });
    }

    return Expr::Constant(Term {
        kind: TermKind::Lit(try_to_bits(ctx, env, ck.ty(), span, ck)),
        ty: ck.ty(),
        span,
    });
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
       let Some(_) = get_builtin(ctx.tcx, u.def.did) {
            return Expr::Constant(Term { kind: TermKind::Lit(Literal::Function(u.def.did, u.substs)), ty: c.ty(), span})
    };

    if let ConstKind::Param(_) = c.kind() {
        ctx.crash_and_error(span, "const generic parameters are not yet supported");
    }

    return Expr::Constant(Term {
        kind: TermKind::Lit(try_to_bits(ctx, env, c.ty(), span, c)),
        ty: c.ty(),
        span,
    });
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
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: ParamEnv<'tcx>, ty: Ty<'tcx>) -> Option<u128> {
        self.try_eval_bits(tcx, env, ty)
    }
}
impl<'tcx> ToBits<'tcx> for ConstantKind<'tcx> {
    fn get_bits(&self, tcx: TyCtxt<'tcx>, env: ParamEnv<'tcx>, ty: Ty<'tcx>) -> Option<u128> {
        self.try_eval_bits(tcx, env, ty)
    }
}
