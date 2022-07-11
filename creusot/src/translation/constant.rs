use creusot_rustc::hir::def_id::DefId;
use creusot_rustc::middle::mir::interpret::{AllocRange, ConstValue};
use creusot_rustc::middle::ty::{Const, ConstKind, ParamEnv, Ty, TyCtxt, Unevaluated};
use creusot_rustc::smir::mir::ConstantKind;
use creusot_rustc::span::Span;
use creusot_rustc::target::abi::Size;
use why3::{
    declaration::Module,
    exp::{Constant, Exp},
    QName,
};

use crate::{
    clone_map::CloneMap,
    ctx::{module_name, CloneSummary, TranslationCtx},
    traits::resolve_assoc_item_opt,
    translation::ty,
    util::get_builtin,
};

impl<'tcx> TranslationCtx<'_, 'tcx> {
    pub fn translate_constant(&mut self, def_id: DefId) -> (Module, CloneSummary<'tcx>) {
        let mut names = CloneMap::new(self.tcx, def_id, false);
        let _ = names.to_clones(self);
        let modl = Module { name: module_name(self.tcx, def_id), decls: Vec::new() };

        (modl, names.summary())
    }
}

pub fn from_mir_constant<'tcx>(
    env: ParamEnv<'tcx>,
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    c: &creusot_rustc::smir::mir::Constant<'tcx>,
) -> Exp {
    from_mir_constant_kind(ctx, names, c.literal, env, c.span)
}

pub fn from_mir_constant_kind<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    ck: creusot_rustc::smir::mir::ConstantKind<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> Exp {
    if let Some(c) = ck.const_for_ty() {
        return from_ty_const(ctx, names, c, env, span);
    }

    if ck.ty().is_unit() {
        return Exp::Tuple(Vec::new());
    }

    if ck.ty().peel_refs().is_str() {
        if let Some(ConstValue::Slice { data, start, end }) = ck.try_to_value(ctx.tcx) {
            let start = Size::from_bytes(start);
            let size = Size::from_bytes(end);
            let bytes = data.inner().get_bytes(&ctx.tcx, AllocRange { start, size }).unwrap();
            let string = std::str::from_utf8(bytes).unwrap();
            return Exp::Const(Constant::String(string.into()));
        }
    }

    return try_to_bits(ctx, names, env, ck.ty(), span, ck);
}

pub fn from_ty_const<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    c: Const<'tcx>,
    env: ParamEnv<'tcx>,
    span: Span,
) -> Exp {
    // Check if a constant is builtin and thus should not be evaluated further
    // Builtin constants are given a body which panics
    if let ConstKind::Unevaluated(u) = c.kind() &&
       let Some(builtin_nm) = get_builtin(ctx.tcx, u.def.did) &&
       let Some(nm) = QName::from_string(builtin_nm.as_str()) {
            names.import_builtin_module(nm.clone().module_qname());
            return Exp::pure_qvar(nm.without_search_path());
    };

    if let ConstKind::Unevaluated(Unevaluated { promoted: Some(p), .. }) = c.kind() {
        return Exp::impure_var(format!("promoted{:?}", p.as_usize()).into());
    }

    if let ConstKind::Param(_) = c.kind() {
        ctx.crash_and_error(span, "const generic parameters are not yet supported");
    }

    return try_to_bits(ctx, names, env, c.ty(), span, c);
}

fn try_to_bits<'tcx, C: ToBits<'tcx>>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
    c: C,
) -> Exp {
    use creusot_rustc::middle::ty::{IntTy::*, UintTy::*};
    use creusot_rustc::type_ir::sty::TyKind::{Bool, FnDef, Int, Uint};
    let why3_ty = ty::translate_ty(ctx, names, span, ty);

    match ty.kind() {
        Int(I128) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Int(bits.unwrap() as i128, Some(why3_ty)))
        }
        Int(I64) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Int(bits.unwrap() as i64 as i128, Some(why3_ty)))
        }
        Int(Isize) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Uint(bits.unwrap() as isize as u128, Some(why3_ty)))
        }
        Int(I32) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Int(bits.unwrap() as i32 as i128, Some(why3_ty)))
        }
        Int(I16) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Int(bits.unwrap() as i16 as i128, Some(why3_ty)))
        }
        Int(I8) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Int(bits.unwrap() as i8 as i128, Some(why3_ty)))
        }
        Uint(U128) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Uint(bits.unwrap(), Some(why3_ty)))
        }
        Uint(Usize) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Uint(bits.unwrap() as usize as u128, Some(why3_ty)))
        }
        Uint(U64) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Uint(bits.unwrap() as u64 as u128, Some(why3_ty)))
        }
        Uint(U32) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Uint(bits.unwrap() as u32 as u128, Some(why3_ty)))
        }
        Uint(U16) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Uint(bits.unwrap() as u16 as u128, Some(why3_ty)))
        }
        Uint(U8) => {
            let bits = c.get_bits(ctx.tcx, env, ty);
            Exp::Const(Constant::Uint(bits.unwrap() as u8 as u128, Some(why3_ty)))
        }
        Bool => {
            if c.get_bits(ctx.tcx, env, ty) == Some(1) {
                Exp::mk_true()
            } else {
                Exp::mk_false()
            }
        }
        _ if ty.is_unit() => Exp::Tuple(Vec::new()),
        FnDef(def_id, subst) => {
            let method =
                resolve_assoc_item_opt(ctx.tcx, env, *def_id, subst).unwrap_or((*def_id, subst));
            names.insert(method.0, method.1);
            Exp::Tuple(Vec::new())
        }
        _ => {
            ctx.crash_and_error(
                span,
                &format!("unsupported constant expression, try binding this to a variable. See issue #163"),
            );
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
