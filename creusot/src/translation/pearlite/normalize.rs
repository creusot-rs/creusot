use crate::{
    contracts_items::get_builtin,
    ctx::{HasTyCtxt as _, TranslationCtx},
    logic_alias::subst_call as subst_alias,
    resolution::TraitResolved,
    translation::pearlite::{
        BinOp, Term, TermKind, UnOp,
        visit::{TermVisitorMut, super_visit_mut_term},
    },
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{EarlyBinder, GenericArgsRef, TypingEnv};

pub(crate) fn normalize<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    mut term: Term<'tcx>,
) -> Term<'tcx> {
    NormalizeTerm { typing_env, ctx }.visit_mut_term(&mut term);
    let term = ctx.normalize_erasing_regions(
        typing_env,
        EarlyBinder::bind(ctx.tcx, term).instantiate_identity(),
    );
    term
}

struct NormalizeTerm<'a, 'tcx> {
    typing_env: TypingEnv<'tcx>,
    ctx: &'a TranslationCtx<'tcx>,
}

impl<'a, 'tcx> TermVisitorMut<'tcx> for NormalizeTerm<'a, 'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        super_visit_mut_term(term, self);
        if let TermKind::Call { id, subst, args } = &mut term.kind {
            let Some(resolved) =
                TraitResolved::resolve_item(self.ctx.tcx, self.typing_env, *id, subst)
                    .to_opt(*id, subst)
            else {
                self.ctx.crash_and_error(
                    term.span,
                    format!(
                        "could not resolve trait instance for {}{}",
                        self.ctx.def_path_str(*id),
                        subst.print_as_list()
                    ),
                )
            };

            (*id, *subst) = resolved;

            if let Some(mut new_term) =
                subst_alias(self.ctx, self.typing_env, *id, subst, args.clone())
            {
                self.visit_mut_term(&mut new_term);
                *term = new_term;
            } else {
                term.kind =
                    optimize_builtin(self.ctx, *id, subst, std::mem::replace(args, Box::new([])));
            }
        }
    }
}

fn optimize_builtin<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    id: DefId,
    subst: GenericArgsRef<'tcx>,
    args: Box<[Term<'tcx>]>,
) -> TermKind<'tcx> {
    use BinOp::*;
    use TermKind::*;
    use UnOp::*;

    if let Some(builtin_str) = get_builtin(ctx.tcx, id).as_ref().map(|s| s.as_str()) {
        if let Some(op) = match builtin_str {
            "int.Int.(+)" => Some(Add),
            "int.Int.(-)" => Some(Sub),
            "int.Int.(*)" => Some(Mul),
            "int.Int.(<=)" => Some(Le),
            "int.Int.(<)" => Some(Lt),
            "int.Int.(>=)" => Some(Ge),
            "int.Int.(>)" => Some(Gt),
            _ => None,
        } {
            let [lhs, rhs] = args.into_array().unwrap().map(Box::new);
            return Binary { op, lhs, rhs };
        }

        match builtin_str {
            "fin" => {
                let [term] = args.into_array().unwrap().map(Box::new);
                return Fin { term };
            }
            "identity" => {
                let [arg] = args.into_array().unwrap().map(Box::new);
                return Coerce { arg };
            }
            "int.Int.(-_)" => {
                let [arg] = args.into_array().unwrap().map(Box::new);
                return Unary { op: Neg, arg };
            }
            "bool.Bool.notb" => {
                let [arg] = args.into_array().unwrap().map(Box::new);
                return Unary { op: Not, arg };
            }
            _ => (),
        }
    }

    return Call { id, subst, args };
}
