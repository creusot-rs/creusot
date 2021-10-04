use super::typing::{LogicalOp, Pattern, Term};
use crate::ctx::*;
use crate::translation::traits::resolve_opt;
use crate::translation::{binop_to_binop, builtins, constant, ty::translate_ty, unop_to_unop};
use why3::mlcfg::{BinOp, Exp, Pattern as Pat};

pub fn lower_term_to_why3<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    term_id: DefId,
    term: Term<'tcx>,
) -> Exp {
    match term {
        Term::Const(c) => Exp::Const(constant::from_mir_constant_kind(ctx, names, c.into())),
        Term::Var(v) => Exp::Var(v.into()),
        Term::Binary { op, box lhs, box rhs } => Exp::BinaryOp(
            binop_to_binop(op),
            box lower_term_to_why3(ctx, names, term_id, lhs),
            box lower_term_to_why3(ctx, names, term_id, rhs),
        ),
        Term::Logical { op, box lhs, box rhs } => Exp::BinaryOp(
            match op {
                LogicalOp::And => BinOp::And,
                LogicalOp::Or => BinOp::Or,
            },
            box lower_term_to_why3(ctx, names, term_id, lhs),
            box lower_term_to_why3(ctx, names, term_id, rhs),
        ),
        Term::Unary { op, box arg } => {
            Exp::UnaryOp(unop_to_unop(op), box lower_term_to_why3(ctx, names, term_id, arg))
        }
        Term::Call { id, subst, fun: box Term::Const(_), args } => {
            let mut args: Vec<_> =
                args.into_iter().map(|arg| lower_term_to_why3(ctx, names, term_id, arg)).collect();

            if args.is_empty() {
                args = vec![Exp::Tuple(vec![])];
            }

            let param_env = ctx.tcx.param_env(term_id);
            let (target, subst) = resolve_opt(ctx.tcx, param_env, id, subst).unwrap_or((id, subst));

            if is_identity_from(ctx.tcx, id, subst) {
                return args.remove(0);
            }

            builtins::lookup_builtin(ctx, target, subst, &mut args).unwrap_or_else(|| {
                ctx.translate_function(target);
                let clone = names.insert(target, subst);
                Exp::Call(box Exp::QVar(clone.qname(ctx.tcx, target)), args)
            })
        }
        Term::Forall { binder, box body } => {
            let ty = translate_ty(ctx, names, rustc_span::DUMMY_SP, binder.1);
            Exp::Forall(
                vec![(binder.0.into(), ty)],
                box lower_term_to_why3(ctx, names, term_id, body),
            )
        }
        Term::Constructor { adt, variant, fields } => {
            names.import_prelude_module(PreludeModule::Type);
            let args =
                fields.into_iter().map(|f| lower_term_to_why3(ctx, names, term_id, f)).collect();

            let ctor = translate_value_id(ctx.tcx, adt.variants[variant].def_id);
            crate::ty::translate_tydecl(ctx, rustc_span::DUMMY_SP, adt.did);
            Exp::Constructor { ctor, args }
        }
        Term::Cur { box term } => Exp::Current(box lower_term_to_why3(ctx, names, term_id, term)),
        Term::Fin { box term } => Exp::Final(box lower_term_to_why3(ctx, names, term_id, term)),
        Term::Impl { box lhs, box rhs } => Exp::Impl(
            box lower_term_to_why3(ctx, names, term_id, lhs),
            box lower_term_to_why3(ctx, names, term_id, rhs),
        ),
        Term::Equals { box lhs, box rhs } => Exp::BinaryOp(
            BinOp::Eq,
            box lower_term_to_why3(ctx, names, term_id, lhs),
            box lower_term_to_why3(ctx, names, term_id, rhs),
        ),
        Term::Match { box scrutinee, arms } => {
            let arms = arms
                .into_iter()
                .map(|(pat, body)| {
                    (
                        lower_pat_to_why3(ctx, names, pat),
                        lower_term_to_why3(ctx, names, term_id, body),
                    )
                })
                .collect();
            Exp::Match(box lower_term_to_why3(ctx, names, term_id, scrutinee), arms)
        }
        Term::Let { pattern, box arg, box body } => Exp::Let {
            pattern: lower_pat_to_why3(ctx, names, pattern),
            arg: box lower_term_to_why3(ctx, names, term_id, arg),
            body: box lower_term_to_why3(ctx, names, term_id, body),
        },
        Term::Tuple { fields } => Exp::Tuple(
            fields.into_iter().map(|f| lower_term_to_why3(ctx, names, term_id, f)).collect(),
        ),
        _ => {
            todo!()
        }
    }
}

pub fn lower_pat_to_why3<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    pat: Pattern<'tcx>,
) -> Pat {
    match pat {
        Pattern::Constructor { adt, variant, fields } => {
            let variant = &adt.variants[variant];
            let fields = fields.into_iter().map(|pat| lower_pat_to_why3(ctx, names, pat)).collect();
            Pat::ConsP(translate_value_id(ctx.tcx, variant.def_id), fields)
        }
        Pattern::Wildcard => Pat::Wildcard,
        Pattern::Binder(name) => Pat::VarP(name.into()),
        Pattern::Boolean(b) => {
            if b {
                Pat::mk_true()
            } else {
                Pat::mk_false()
            }
        }
        Pattern::Tuple(pats) => {
            Pat::TupleP(pats.into_iter().map(|pat| lower_pat_to_why3(ctx, names, pat)).collect())
        }
        #[allow(unreachable_patterns)]
        _ => todo!("{:?}", pat),
    }
}

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    subst::{Subst, SubstsRef},
    TyCtxt,
};

fn is_identity_from<'tcx>(tcx: TyCtxt<'tcx>, id: DefId, subst: SubstsRef<'tcx>) -> bool {
    if tcx.def_path_str(id) == "std::convert::From::from" && subst.len() == 1 {
        let out_ty = tcx.fn_sig(id).no_bound_vars().unwrap().output();
        return subst[0].expect_ty() == out_ty.subst(tcx, subst);
    }
    false
}
