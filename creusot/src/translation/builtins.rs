use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    subst::{InternalSubsts, Subst, SubstsRef},
    TyCtxt,
};
use rustc_span::{symbol::sym, Symbol};
use why3::{
    mlcfg::{BinOp, Exp, UnOp},
    QName,
};

use crate::ctx::TranslationCtx;

use super::traits::resolve_opt;

pub fn lookup_builtin(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    mut def_id: DefId,
    substs: SubstsRef<'tcx>,
    args: &mut Vec<Exp>,
) -> Option<Exp> {
    if let Some(trait_id) = trait_id_of_method(ctx.tcx, def_id) {
        // We typically implement `From` but call `into`, using the blanket impl of `Into`
        // for any `From` type. So when we see an instance of `into` we check that isn't just
        // a wrapper for a builtin `From` impl.
        if ctx.tcx.is_diagnostic_item(sym::into_trait, trait_id) {
            let from_fn = ctx.tcx.lang_items().from_fn().unwrap();
            let from_subst = ctx.tcx.intern_substs(&[substs[1], substs[0]]);
            let from_impl =
                resolve_opt(ctx.tcx, ctx.tcx.param_env(def_id), from_fn, from_subst).unwrap();
            def_id = from_impl.0;
        }
    }

    let def_id = Some(def_id);

    if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("add_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Add, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("sub_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Sub, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("mul_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Mul, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("div_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Div, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("rem_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Mod, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("neg_int")) {
        let a = args.remove(0);

        return Some(Exp::UnaryOp(UnOp::Neg, box a));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("le_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Le, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("lt_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Lt, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("ge_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Ge, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("gt_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Gt, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("eq_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Eq, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("ne_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Ne, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("u32_to_int")) {
        let i = args.remove(0);
        return Some(Exp::Call(
            box Exp::QVar(QName::from_string("UInt32.to_int").unwrap()),
            vec![i],
        ));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("i32_to_int")) {
        let i = args.remove(0);
        return Some(Exp::Call(
            box Exp::QVar(QName::from_string("Int32.to_int").unwrap()),
            vec![i],
        ));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("usize_to_int")) {
        let i = args.remove(0);
        return Some(Exp::Call(
            box Exp::QVar(QName::from_string("UInt64.to_int").unwrap()),
            vec![i],
        ));
    }
    None
}

fn trait_id_of_method(tcx: TyCtxt, def_id: DefId) -> Option<DefId> {
    tcx.impl_of_method(def_id).and_then(|id| tcx.trait_id_of_impl(id))
}
