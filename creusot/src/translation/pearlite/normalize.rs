use crate::{
    contracts_items::{Intrinsic, get_builtin},
    ctx::TranslationCtx,
    translation::{
        pearlite::{
            BinOp, Literal, Term, TermKind, UnOp,
            visit::{TermVisitorMut, super_visit_mut_term},
        },
        traits::TraitResolved,
    },
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgsRef, TypingEnv};
use rustc_span::sym;

pub(crate) fn normalize<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    mut term: Term<'tcx>,
) -> Term<'tcx> {
    NormalizeTerm { typing_env, ctx }.visit_mut_term(&mut term);
    let term = ctx.normalize_erasing_regions(typing_env, term);
    term
}

struct NormalizeTerm<'a, 'tcx> {
    typing_env: TypingEnv<'tcx>,
    ctx: &'a TranslationCtx<'tcx>,
}

impl<'a, 'tcx> TermVisitorMut<'tcx> for NormalizeTerm<'a, 'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        super_visit_mut_term(term, self);
        match &mut term.kind {
            TermKind::Call { id, subst, args } => {
                (*id, *subst) =
                    TraitResolved::resolve_item(self.ctx.tcx, self.typing_env, *id, subst)
                        .to_opt(*id, subst)
                        .unwrap_or_else(|| {
                            panic!("could not resolve trait instance {:?}", (*id, *subst))
                        });
                term.kind =
                    optimize_builtin(self.ctx, *id, subst, std::mem::replace(args, Box::new([])));
            }
            TermKind::Item(id, subst) => {
                (*id, *subst) =
                    TraitResolved::resolve_item(self.ctx.tcx, self.typing_env, *id, subst)
                        .to_opt(*id, subst)
                        .unwrap_or_else(|| {
                            panic!("could not resolve trait instance {:?}", (*id, *subst))
                        })
            }
            _ => {}
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
    use Literal::*;
    use TermKind::*;
    use UnOp::*;

    let builtin = get_builtin(ctx.tcx, id);
    let builtin_str = builtin.as_ref().map(|s| s.as_str());

    if let Some(op) = match builtin_str {
        Some("mach.int.Int.(+)") => Some(Add),
        Some("mach.int.Int.(-)") => Some(Sub),
        Some("mach.int.Int.(*)") => Some(Mul),
        Some("mach.int.Int.(<=)") => Some(Le),
        Some("mach.int.Int.(<)") => Some(Lt),
        Some("mach.int.Int.(>=)") => Some(Ge),
        Some("mach.int.Int.(>)") => Some(Gt),
        _ => None,
    } {
        let [lhs, rhs] = args.into_array().unwrap().map(Box::new);
        return Binary { op, lhs, rhs };
    }

    match builtin_str {
        None if ctx.is_diagnostic_item(sym::box_new, id)
            || matches!(ctx.intrinsic(id), Intrinsic::GhostDeref | Intrinsic::GhostDerefMut) =>
        {
            let [arg] = *args.into_array::<1>().unwrap();
            return Coerce { arg: Box::new(arg) };
        }
        Some("fin") => {
            let [arg] = *args.into_array::<1>().unwrap();
            return Fin { term: Box::new(arg) };
        }
        Some("identity") => {
            let [arg] = *args.into_array::<1>().unwrap();
            return Coerce { arg: Box::new(arg) };
        }
        Some("mach.int.Int.(-_)") => {
            let [arg] = *args.into_array::<1>().unwrap();
            return Unary { op: Neg, arg: Box::new(arg) };
        }
        Some(
            "creusot.int.UInt8$BW$.t'int"
            | "creusot.int.UInt16$BW$.t'int"
            | "creusot.int.UInt32$BW$.t'int"
            | "creusot.int.UInt64$BW$.t'int"
            | "creusot.int.UInt128$BW$.t'int",
        ) if let box [Term { kind: Lit(MachUnsigned(c, _)), .. }] = args => {
            return Lit(UInteger(c));
        }
        Some(
            "creusot.int.Int8$BW$.to_int"
            | "creusot.int.Int16$BW$.to_int"
            | "creusot.int.Int32$BW$.to_int"
            | "creusot.int.Int64$BW$.to_int"
            | "creusot.int.Int128$BW$.to_int",
        ) if let box [Term { kind: Lit(MachSigned(c, _)), .. }] = args => return Lit(Integer(c)),
        _ => (),
    }

    return Call { id, subst, args };
}
