use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Const, ConstKind, ParamEnv, Ty, Unevaluated};
use rustc_span::Span;
use why3::{
    declaration::Module,
    mlcfg::{self, Constant, Exp},
    QName,
};

use crate::{
    clone_map::CloneMap,
    ctx::{module_name, CloneSummary, TranslationCtx},
    translation::ty,
    util::get_builtin,
};

impl TranslationCtx<'_, 'tcx> {
    pub fn translate_constant(&mut self, def_id: DefId) -> (Module, CloneSummary<'tcx>) {
        let names = CloneMap::new(self.tcx, def_id, false);

        let modl = Module { name: module_name(self.tcx, def_id), decls: Vec::new() };

        (modl, names.summary())
    }
}

pub fn from_mir_constant<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    _id: DefId,
    c: &rustc_middle::mir::Constant<'tcx>,
) -> mlcfg::Exp {
    from_mir_constant_kind(ctx, names, c.literal, _id, c.span)
}

pub fn from_mir_constant_kind<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    ck: rustc_middle::mir::ConstantKind<'tcx>,
    _id: DefId,
    span: Span,
) -> mlcfg::Exp {
    if let Some(c) = ck.const_for_ty() {
        return from_ty_const(ctx, names, c, ctx.param_env(_id), span);
    }

    ctx.crash_and_error(span, "unsupported constant expression")
}

fn from_ty_const(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    c: &Const<'tcx>,
    env: ParamEnv<'tcx>,
    // ty: Ty<'tcx>,
    span: Span,
) -> Exp {
    // Check if a constant is builtin and thus should not be evaluated further
    // Builtin constants are given a body which panics
    if let ConstKind::Unevaluated(u) = c.val &&
       let Some(builtin_nm) = get_builtin(ctx.tcx, u.def.did) &&
       let Some(nm) = QName::from_string(builtin_nm.as_str()) {
            return Exp::pure_qvar(nm.without_search_path());
    };

    // Normalize the constant?
    match c.val.eval(ctx.tcx, env) {
        ConstKind::Value(v) => {
            use rustc_middle::ty::TyKind::{Bool, Int, Uint};
            use rustc_middle::ty::{IntTy::*, UintTy::*};
            let why3_ty = ty::translate_ty(ctx, names, span, c.ty);

            match c.ty.kind() {
                Int(I128) => unimplemented!("128-bit integers are not supported"),
                Int(_) => {
                    let bits = c.try_eval_bits(ctx.tcx, env, c.ty);
                    Exp::Const(Constant::Int(
                        i128::from_be_bytes(bits.unwrap().to_be_bytes()),
                        Some(why3_ty),
                    ))
                }
                Uint(U128) => unimplemented!("128-bit integers are not supported"),
                Uint(_) => {
                    let bits = c.try_eval_bits(ctx.tcx, env, c.ty);
                    Exp::Const(Constant::Uint(bits.unwrap(), Some(why3_ty)))
                }
                Bool => {
                    if c.val.try_to_bool().unwrap() {
                        Exp::mk_true()
                    } else {
                        Exp::mk_false()
                    }
                }
                _ if c.ty.is_unit() => Exp::Tuple(Vec::new()),
                _ => {
                    ctx.crash_and_error(
                span,
                &format!("unsupported constant expression, try binding this to a variable. See issue #163"),
            );
                }
            }
        }
        _ => ctx.crash_and_error(
            span,
            "unsupported constant expression, try binding this to a variable. See issue #163",
        ),
    }
}
