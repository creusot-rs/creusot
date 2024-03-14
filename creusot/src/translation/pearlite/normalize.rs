use crate::{
    pearlite::{self, Literal, Term, TermKind},
    translation::traits::resolve_opt,
    util::get_builtin,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{ParamEnv, TyCtxt};
use rustc_span::{symbol::sym, Symbol};

use super::{super_visit_mut_term, BinOp, TermVisitorMut};

pub(crate) fn normalize<'tcx>(tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>, term: &mut Term<'tcx>) {
    NormalizeTerm { param_env, tcx }.visit_mut_term(term);
}

struct NormalizeTerm<'tcx> {
    param_env: ParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TermVisitorMut<'tcx> for NormalizeTerm<'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        super_visit_mut_term(term, self);
        match &mut term.kind {
            TermKind::Call { id, subst, args } => {
                let method = if self.tcx.trait_of_item(*id).is_some() {
                    resolve_opt(self.tcx, self.param_env, *id, subst).unwrap_or_else(|| {
                        panic!("could not resolve trait instance {:?}", (*id, *subst))
                    })
                } else {
                    // TODO dont' do this
                    (*id, *subst)
                };
                *id = method.0;
                *subst = method.1;
                *subst = self.tcx.normalize_erasing_regions(self.param_env, *subst);

                if self.tcx.def_path_str(*id) == "std::boxed::Box::<T>::new" {
                    let arg = args.remove(0);
                    *term = arg;
                    return;
                }

                if let Some(opt) = optimize_builtin(self.tcx, *id, args) {
                    term.kind = opt;
                }
            }
            TermKind::Item(id, subst) => {
                let method = if self.tcx.trait_of_item(*id).is_some() {
                    resolve_opt(self.tcx, self.param_env, *id, subst).unwrap_or_else(|| {
                        panic!("could not resolve trait instance {:?}", (*id, *subst))
                    })
                } else {
                    // TODO dont' do this
                    (*id, *subst)
                };
                *id = method.0;
                *subst = method.1;
            }
            _ => {}
        }
    }
}

fn optimize_builtin<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    args: &mut Vec<Term<'tcx>>,
) -> Option<TermKind<'tcx>> {
    let builtin_attr = get_builtin(tcx, def_id);

    if builtin_attr == Some(Symbol::intern("add_int")) {
        Some(TermKind::Binary {
            op: BinOp::Add,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("sub_int")) {
        Some(TermKind::Binary {
            op: BinOp::Sub,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("mul_int")) {
        Some(TermKind::Binary {
            op: BinOp::Mul,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("div_int")) {
        Some(TermKind::Binary {
            op: BinOp::Div,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("rem_int")) {
        Some(TermKind::Binary {
            op: BinOp::Rem,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("neg_int")) {
        Some(TermKind::Unary { op: pearlite::UnOp::Neg, arg: Box::new(args.remove(0)) })
    } else if builtin_attr == Some(Symbol::intern("int.Int.(<=)")) {
        Some(TermKind::Binary {
            op: BinOp::Le,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("int.Int.(<)")) {
        Some(TermKind::Binary {
            op: BinOp::Lt,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("int.Int.(>=)")) {
        Some(TermKind::Binary {
            op: BinOp::Ge,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("int.Int.(>)")) {
        Some(TermKind::Binary {
            op: BinOp::Gt,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("==")) {
        Some(TermKind::Binary {
            op: BinOp::Eq,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("!=")) {
        Some(TermKind::Binary {
            op: BinOp::Ne,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        })
    } else if builtin_attr == Some(Symbol::intern("prelude.UInt8.to_int"))
        && let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.UInt16.to_int"))
        && let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.UInt32.to_int"))
        && let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.UInt64.to_int"))
        && let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.UInt128.to_int"))
        && let TermKind::Lit(Literal::MachUnsigned(c, _)) = args[0].kind
    {
        if c > isize::MAX as u128 {
            panic!("integer constant too large")
        }
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.Int8.to_int"))
        && let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.Int16.to_int"))
        && let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.Int32.to_int"))
        && let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.Int64.to_int"))
        && let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("prelude.Int128.to_int"))
        && let TermKind::Lit(Literal::MachSigned(c, _)) = args[0].kind
    {
        Some(TermKind::Lit(Literal::Integer(c as i128)))
    } else if builtin_attr == Some(Symbol::intern("identity")) {
        Some(args.remove(0).kind)
    } else if Some(def_id) == tcx.get_diagnostic_item(sym::unreachable) {
        Some(TermKind::Absurd)
    } else if Some(def_id) == tcx.get_diagnostic_item(sym::abort) {
        Some(TermKind::Absurd)
    } else {
        None
    }
}
