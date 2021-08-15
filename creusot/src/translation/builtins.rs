use rustc_hir::def_id::DefId;
use rustc_span::Symbol;
use why3::mlcfg::{BinOp, Exp, QName};

use crate::ctx::TranslationCtx;

pub fn lookup_builtin(
    ctx: &mut TranslationCtx<'_, '_>,
    def_id: DefId,
    args: &mut Vec<Exp>,
) -> Option<Exp> {
    let def_id = Some(def_id);

    if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("equal")) {
        let l = args.remove(0);
        let r = args.remove(0);
        return Some(Exp::BinaryOp(BinOp::Eq, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("absurd")) {
        return Some(Exp::Absurd);
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("add_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Add, box l, box r));
    } else if def_id == ctx.tcx.get_diagnostic_item(Symbol::intern("sub_int")) {
        let l = args.remove(0);
        let r = args.remove(0);

        return Some(Exp::BinaryOp(BinOp::Sub, box l, box r));
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
