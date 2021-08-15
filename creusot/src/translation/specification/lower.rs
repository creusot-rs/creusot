use crate::ctx::*;
use crate::rustc_extensions;
use crate::translation::binop_to_binop;
use crate::translation::builtins;
use crate::translation::constant;
use crate::translation::ty::translate_ty;
use creusot_contracts::typing::{LogicalOp, Pattern, Term};
use why3::mlcfg::{BinOp, Exp, Pattern as Pat, QName};

pub fn lower_term_to_why3<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut NameMap<'tcx>,
    term_id: DefId,
    term: Term<'tcx>,
) -> Exp {
    match term {
        Term::Const(c) => Exp::Const(constant::from_mir_constant_kind(ctx.tcx, c.into())),
        Term::Var(v) => Exp::Var(v.into()),
        Term::Binary { op, box lhs, box rhs } => Exp::BinaryOp(
            binop_to_binop(op),
            box lower_term_to_why3(ctx, names, term_id, lhs),
            box lower_term_to_why3(ctx, names, term_id, rhs),
        ),
        Term::Call { id, subst, fun: box Term::Const(_), args } => {
            let mut args: Vec<_> =
                args.into_iter().map(|arg| lower_term_to_why3(ctx, names, term_id, arg)).collect();

            if args.is_empty() {
                args = vec![Exp::Tuple(vec![])];
            }

            let params = ctx.tcx.param_env(id);

            let target = match rustc_extensions::resolve_instance(ctx.tcx, params.and((id, subst)))
            {
                Ok(Some(inst)) => inst.def_id(),
                Ok(_) => id,
                Err(mut err) => {
                    err.cancel();
                    id
                }
            };

            if is_identity_from(ctx.tcx, id, subst) {
                return args.remove(0);
            }

            builtins::lookup_builtin(ctx, target, &mut args).unwrap_or_else(|| {
                if target == term_id {
                    Exp::Call(box Exp::Var("impl".into()), args)
                } else {
                    let clone = names.name_for(target, subst);
                    let fname = QName { module: vec![clone], name: "impl".into() };
                    Exp::Call(box Exp::QVar(fname), args)
                }
            })
        }
        Term::Forall { binder, box body } => {
            let ty = translate_ty(ctx, rustc_span::DUMMY_SP, binder.1);
            Exp::Forall(
                vec![(binder.0.into(), ty)],
                box lower_term_to_why3(ctx, names, term_id, body),
            )
        }
        Term::Logical { op, box lhs, box rhs } => {
            let op = match op {
                LogicalOp::And => BinOp::And,
                LogicalOp::Or => BinOp::Or,
            };

            Exp::BinaryOp(
                op,
                box lower_term_to_why3(ctx, names, term_id, lhs),
                box lower_term_to_why3(ctx, names, term_id, rhs),
            )
        }
        Term::Constructor { adt, variant, fields } => {
            let args =
                fields.into_iter().map(|f| lower_term_to_why3(ctx, names, term_id, f)).collect();

            let ctor = translate_value_id(ctx.tcx, adt.variants[variant].def_id);
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
        _ => {
            todo!()
        }
    }
}

pub fn lower_pat_to_why3<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut NameMap<'tcx>,
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
        _ => todo!(),
    }
}

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{subst::SubstsRef, TyCtxt};

fn is_identity_from<'tcx>(tcx: TyCtxt<'tcx>, id: DefId, subst: SubstsRef<'tcx>) -> bool {
    tcx.def_path_str(id) == "std::convert::From::from" && subst[0] == subst[1]
}
