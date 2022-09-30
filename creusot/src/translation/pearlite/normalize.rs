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
    util::constructor_qname,
};
use creusot_rustc::{
    hir::Unsafety,
    middle::{
        ty,
        ty::{EarlyBinder, ParamEnv, Subst},
    },
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::{super_visit_mut_term, TermVisitor, TermVisitorMut};

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
                fun,
                // fun: box Term { kind: TermKind::Item(id, subst), .. },
                args,
            } => {
                // Temporary: until we get rid of id, subst in call.
                let method = if self.tcx.trait_of_item(*id).is_some() {
                    resolve_opt(self.tcx, self.param_env, *id, subst)
                        .expect("could not resolve trait instance")
                } else {
                    // TODO dont' do this
                    resolve_opt(self.tcx, self.param_env, *id, subst).unwrap_or((*id, subst))
                };
                // eprintln!("normalize: {:?} {:?}", method.0, method.1);
                *id = method.0;
                *subst = method.1;
            }
            TermKind::Item(id, subst) => {
                let method = if self.tcx.trait_of_item(*id).is_some() {
                    resolve_opt(self.tcx, self.param_env, *id, subst)
                        .expect("could not resolve trait instance")
                } else {
                    // TODO dont' do this
                    resolve_opt(self.tcx, self.param_env, *id, subst).unwrap_or((*id, subst))
                };
                *id = method.0;
                *subst = method.1;
            }
            _ => {}
        }
    }
}
