use crate::{
    ctx::*,
    pearlite::{self, Literal, Pattern, Term, TermKind},
    translation::{
        traits::{resolve_assoc_item_opt, resolve_opt},
        ty::{
            closure_accessor_name, intty_to_ty, translate_ty, uintty_to_ty, variant_accessor_name,
        },
    },
    util,
    util::{constructor_qname, get_builtin},
};
use creusot_rustc::{
    hir::{def_id::DefId, Unsafety},
    middle::{
        ty,
        ty::{subst::SubstsRef, EarlyBinder, ParamEnv, Subst, TyCtxt},
    },
    span::{symbol::sym, Span, Symbol},
};
use rustc_middle::ty::{Ty, TyKind};

use super::{super_visit_mut_term, BinOp, TermVisitor, TermVisitorMut};

pub(crate) fn normalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    mut term: Term<'tcx>,
) -> Term<'tcx> {
    NormalizeTerm { param_env, tcx }.visit_mut_term(&mut term);
    term
}

struct NormalizeTerm<'tcx> {
    param_env: ParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TermVisitorMut<'tcx> for NormalizeTerm<'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        super_visit_mut_term(term, self);
        match &mut term.kind {
            TermKind::Call {
                id,
                subst,
                fun: box Term { kind: TermKind::Item(fid, fsubst), .. },
                args,
            } => {
                *id = *fid;
                *subst = fsubst;

                if let Some(opt) = optimize_builtin(self.tcx, *id, *subst, args) {
                    term.kind = opt;
                }
            }
            TermKind::Item(id, subst) => {
                let method = if self.tcx.trait_of_item(*id).is_some() {
                    resolve_opt(self.tcx, self.param_env, *id, subst)
                        .expect("could not resolve trait instance")
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
    substs: SubstsRef<'tcx>,
    args: &mut Vec<Term<'tcx>>,
) -> Option<TermKind<'tcx>> {
    let builtin_attr = get_builtin(tcx, def_id);

    if builtin_attr == Some(Symbol::intern("add_int")) {
        Some(TermKind::Binary { op: BinOp::Add, lhs: box args.remove(0), rhs: box args.remove(0) })
    } else if builtin_attr == Some(Symbol::intern("sub_int")) {
        Some(TermKind::Binary { op: BinOp::Sub, lhs: box args.remove(0), rhs: box args.remove(0) })
    } else if builtin_attr == Some(Symbol::intern("mul_int")) {
        Some(TermKind::Binary { op: BinOp::Mul, lhs: box args.remove(0), rhs: box args.remove(0) })
    } else if builtin_attr == Some(Symbol::intern("div_int")) {
        Some(TermKind::Binary { op: BinOp::Div, lhs: box args.remove(0), rhs: box args.remove(0) })
    } else if builtin_attr == Some(Symbol::intern("rem_int")) {
        Some(TermKind::Binary { op: BinOp::Rem, lhs: box args.remove(0), rhs: box args.remove(0) })
    } else if builtin_attr == Some(Symbol::intern("neg_int")) {
        Some(TermKind::Unary { op: pearlite::UnOp::Neg, arg: box args.remove(0) })
    // } else if builtin_attr == Some(Symbol::intern("int.Int.(<=)")) {
    // } else if builtin_attr == Some(Symbol::intern("int.Int.(<)")) {
    // } else if builtin_attr == Some(Symbol::intern("int.Int.(>=)")) {
    // } else if builtin_attr == Some(Symbol::intern("int.Int.(>)")) {
    } else if builtin_attr == Some(Symbol::intern("==")) {
        Some(TermKind::Binary { op: BinOp::Eq, lhs: box args.remove(0), rhs: box args.remove(0) })
    } else if builtin_attr == Some(Symbol::intern("!=")) {
        Some(TermKind::Binary { op: BinOp::Ne, lhs: box args.remove(0), rhs: box args.remove(0) })
    // } else if builtin_attr == Some(Symbol::intern("mach.int.UInt8.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.UInt16.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.UInt32.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.UInt64.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.UInt128.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.Int8.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.Int16.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.Int32.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.Int64.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("mach.int.Int128.to_int")) {
    // } else if builtin_attr == Some(Symbol::intern("ghost_new")) {

    //     // } else if builtin_attr == Some(Symbol::intern("ghost_inner")) {
    // } else if builtin_attr == Some(Symbol::intern("ghost_deref")) {
    // } else if builtin_attr == Some(Symbol::intern("identity")) {
    } else {
        None
    }
}
