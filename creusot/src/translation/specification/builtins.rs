use super::lower::mk_binders;
use super::lower::Lower;
use crate::translation::traits::resolve_opt;
use crate::translation::ty::translate_ty;
use crate::util::get_builtin;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{subst::SubstsRef, TyCtxt};
use rustc_span::{symbol::sym, Symbol};
use why3::mlcfg::{BinOp, Constant, Exp, Purity, UnOp};
use why3::QName;

impl<'tcx> Lower<'_, '_, 'tcx> {
    pub fn lookup_builtin(
        &mut self,
        method: (DefId, SubstsRef<'tcx>),
        args: &mut Vec<Exp>,
    ) -> Option<Exp> {
        let mut def_id = method.0;
        let substs = method.1;
        if let Some(trait_id) = trait_id_of_method(self.ctx.tcx, def_id) {
            // We typically implement `From` but call `into`, using the blanket impl of `Into`
            // for any `From` type. So when we see an instance of `into` we check that isn't just
            // a wrapper for a builtin `From` impl.
            if self.ctx.tcx.is_diagnostic_item(sym::Into, trait_id) {
                let from_fn = self.ctx.tcx.lang_items().from_fn().unwrap();
                let from_subst = self.ctx.tcx.intern_substs(&[substs[1], substs[0]]);
                let from_impl =
                    resolve_opt(self.ctx.tcx, self.ctx.tcx.param_env(def_id), from_fn, from_subst)
                        .unwrap();
                def_id = from_impl.0;
            }
        }

        let def_id = Some(def_id);
        let builtin_attr = get_builtin(self.ctx.tcx, def_id.unwrap());

        if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("add_int")) {
            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Add, box l, box r));
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("sub_int")) {
            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Sub, box l, box r));
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("mul_int")) {
            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Mul, box l, box r));
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("div_int")) {
            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::Call(box Exp::pure_var("div".into()), vec![l, r]));
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("rem_int")) {
            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::Call(box Exp::pure_var("Int.mod".into()), vec![l, r]));
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("neg_int")) {
            let a = args.remove(0);

            return Some(Exp::UnaryOp(UnOp::Neg, box a));
        } else if builtin_attr == Some(Symbol::intern("<=")) {
            let ty = self.ctx.tcx.fn_sig(def_id.unwrap()).no_bound_vars().unwrap().inputs()[0];
            translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty);

            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Le, box l, box r));
        } else if builtin_attr == Some(Symbol::intern("<")) {
            let ty = self.ctx.tcx.fn_sig(def_id.unwrap()).no_bound_vars().unwrap().inputs()[0];
            translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty);

            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Lt, box l, box r));
        } else if builtin_attr == Some(Symbol::intern(">=")) {
            let ty = self.ctx.tcx.fn_sig(def_id.unwrap()).no_bound_vars().unwrap().inputs()[0];
            translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty);

            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Ge, box l, box r));
        } else if builtin_attr == Some(Symbol::intern(">")) {
            let ty = self.ctx.tcx.fn_sig(def_id.unwrap()).no_bound_vars().unwrap().inputs()[0];
            translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty);

            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Gt, box l, box r));
        } else if builtin_attr == Some(Symbol::intern("==")) {
            let ty = self.ctx.tcx.fn_sig(def_id.unwrap()).no_bound_vars().unwrap().inputs()[0];
            translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty);

            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Eq, box l, box r));
        } else if builtin_attr == Some(Symbol::intern("!=")) {
            let ty = self.ctx.tcx.fn_sig(def_id.unwrap()).no_bound_vars().unwrap().inputs()[0];
            translate_ty(self.ctx, self.names, rustc_span::DUMMY_SP, ty);

            let l = args.remove(0);
            let r = args.remove(0);

            return Some(Exp::BinaryOp(BinOp::Ne, box l, box r));
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("u32_to_int"))
            || def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("u32_model"))
        {
            if let Exp::Const(Constant::Uint(v, _)) = args[0] {
                return Some(Exp::Const(Constant::Uint(v, None)));
            } else if !self.ctx.opts.bounds_check {
                return Some(args.remove(0));
            }
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("i32_to_int"))
            || def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("i32_model"))
        {
            if let Exp::Const(Constant::Int(v, _)) = args[0] {
                return Some(Exp::Const(Constant::Int(v, None)));
            } else if !self.ctx.opts.bounds_check {
                return Some(args.remove(0));
            }
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("usize_to_int"))
            || def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("usize_model"))
        {
            if let Exp::Const(Constant::Uint(v, _)) = args[0] {
                return Some(Exp::Const(Constant::Uint(v, None)));
            } else if !self.ctx.opts.bounds_check {
                return Some(args.remove(0));
            }
        } else if def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("isize_to_int"))
            || def_id == self.ctx.tcx.get_diagnostic_item(Symbol::intern("isize_model"))
        {
            if let Exp::Const(Constant::Int(v, _)) = args[0] {
                return Some(Exp::Const(Constant::Int(v, None)));
            } else if !self.ctx.opts.bounds_check {
                return Some(args.remove(0));
            }
        } else if def_id == self.ctx.tcx.get_diagnostic_item(sym::abort) {
            // Semi-questionable: we allow abort() & unreachable() in pearlite but
            // interpret them as `absurd` (aka prove false).
            return Some(Exp::Absurd);
        } else if def_id == self.ctx.tcx.get_diagnostic_item(sym::unreachable) {
            return Some(Exp::Absurd);
        } else if self.ctx.tcx.def_path_str(def_id.unwrap()) == "std::boxed::Box::<T>::new" {
            return Some(args.remove(0));
        }

        if let Some(builtin) = builtin_attr.and_then(|a| QName::from_string(&a.as_str())) {
            self.names.import_builtin_module(builtin.clone().module_qname());

            if let Purity::Program = self.pure {
                return Some(mk_binders(
                    Exp::pure_qvar(builtin.without_search_path()),
                    args.clone(),
                ));
            } else {
                return Some(Exp::Call(
                    box Exp::pure_qvar(builtin.without_search_path()),
                    args.clone(),
                ));
            }
        }
        None
    }
}

fn trait_id_of_method(tcx: TyCtxt, def_id: DefId) -> Option<DefId> {
    tcx.impl_of_method(def_id).and_then(|id| tcx.trait_id_of_impl(id))
}
