use rustc_resolve::Namespace;
use why3::mlcfg::{self, Constant};

use crate::{clone_map::CloneMap, ctx::TranslationCtx, translation::ty};

pub fn from_mir_constant<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    c: &rustc_middle::mir::Constant<'tcx>,
) -> mlcfg::Constant {
    from_mir_constant_kind(ctx, names, c.literal)
}

pub fn from_mir_constant_kind<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    ck: rustc_middle::mir::ConstantKind<'tcx>,
) -> mlcfg::Constant {
    use rustc_middle::ty::TyKind::{Int, Uint};
    use rustc_middle::ty::{IntTy::*, UintTy::*};
    use rustc_target::abi::Size;

    let ty = ty::translate_ty(ctx, names, rustc_span::DUMMY_SP, ck.ty());
    match ck.ty().kind() {
        Int(I8) => Constant::Int(ck.try_to_bits(Size::from_bytes(1)).unwrap() as i128, Some(ty)),
        Int(I16) => Constant::Int(ck.try_to_bits(Size::from_bytes(2)).unwrap() as i128, Some(ty)),
        Int(I32) => Constant::Int(ck.try_to_bits(Size::from_bytes(4)).unwrap() as i128, Some(ty)),
        Int(I64) => Constant::Int(ck.try_to_bits(Size::from_bytes(8)).unwrap() as i128, Some(ty)),
        Int(I128) => unimplemented!("128-bit integers are not supported"),

        Uint(U8) => Constant::Uint(ck.try_to_bits(Size::from_bytes(1)).unwrap(), Some(ty)),
        Uint(U16) => Constant::Uint(ck.try_to_bits(Size::from_bytes(2)).unwrap(), Some(ty)),
        Uint(U32) => Constant::Uint(ck.try_to_bits(Size::from_bytes(4)).unwrap(), Some(ty)),
        Uint(U64) => Constant::Uint(ck.try_to_bits(Size::from_bytes(8)).unwrap(), Some(ty)),
        Uint(U128) => {
            unimplemented!("128-bit integers are not supported")
        }
        Uint(Usize) => Constant::Uint(ck.try_to_bits(Size::from_bytes(8)).unwrap(), Some(ty)),
        _ => {
            use rustc_middle::ty::print::{FmtPrinter, PrettyPrinter};
            let mut fmt = String::new();
            let cx = FmtPrinter::new(ctx.tcx, &mut fmt, Namespace::ValueNS);
            // cx.pretty_print_const(ck, false).unwrap();
            use rustc_middle::mir::ConstantKind;
            match ck {
                ConstantKind::Ty(c) => cx.pretty_print_const(c, false).unwrap(),
                ConstantKind::Val(val, ty) => cx.pretty_print_const_value(val, ty, false).unwrap(),
            };

            Constant::Other(fmt)
        }
    }
}
