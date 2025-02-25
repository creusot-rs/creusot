use crate::{
    contracts_items::{get_builtin, is_box_new},
    pearlite::{BinOp, Literal, Term, TermKind, TermVisitorMut, UnOp, super_visit_mut_term},
    traits::TraitResolved,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgsRef, TyCtxt, TypingEnv};

pub(crate) fn normalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    mut term: Term<'tcx>,
) -> Term<'tcx> {
    NormalizeTerm { typing_env, tcx }.visit_mut_term(&mut term);
    let term = tcx.normalize_erasing_regions(typing_env, term);
    term
}

struct NormalizeTerm<'tcx> {
    typing_env: TypingEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TermVisitorMut<'tcx> for NormalizeTerm<'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        super_visit_mut_term(term, self);
        match &mut term.kind {
            TermKind::Call { id, subst, args } => {
                if self.tcx.trait_of_item(*id).is_some() {
                    let method = TraitResolved::resolve_item(self.tcx, self.typing_env, *id, subst)
                        .to_opt(*id, subst)
                        .unwrap_or_else(|| {
                            panic!("could not resolve trait instance {:?}", (*id, *subst))
                        });
                    *id = method.0;
                    *subst = method.1;
                }

                term.kind =
                    optimize_builtin(self.tcx, *id, subst, std::mem::replace(args, Box::new([])));
            }
            TermKind::Item(id, subst) => {
                if self.tcx.trait_of_item(*id).is_some() {
                    let method = TraitResolved::resolve_item(self.tcx, self.typing_env, *id, subst)
                        .to_opt(*id, subst)
                        .unwrap_or_else(|| {
                            panic!("could not resolve trait instance {:?}", (*id, *subst))
                        });
                    *id = method.0;
                    *subst = method.1;
                }
            }
            _ => {}
        }
    }
}

fn optimize_builtin<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: DefId,
    subst: GenericArgsRef<'tcx>,
    args: Box<[Term<'tcx>]>,
) -> TermKind<'tcx> {
    use BinOp::*;
    use Literal::*;
    use TermKind::*;
    use UnOp::*;

    let builtin = get_builtin(tcx, id);
    let builtin_str = builtin.as_ref().map(|s| s.as_str());

    if let Some(op) = match builtin_str {
        Some("mach.int.Int.(+)") => Some(Add),
        Some("mach.int.Int.(-)") => Some(Sub),
        Some("mach.int.Int.(*)") => Some(Mul),
        Some("mach.int.Int.(/)") => Some(Div),
        Some("mach.int.Int.(%)") => Some(Rem),
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
        None if is_box_new(tcx, id) => {
            let [arg] = *args.into_array::<1>().unwrap();
            return Coerce { arg: Box::new(arg) };
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
            "prelude.int.UInt8$BW$.t'int"
            | "prelude.int.UInt16$BW$.t'int"
            | "prelude.int.UInt32$BW$.t'int"
            | "prelude.int.UInt64$BW$.t'int"
            | "prelude.int.UInt128$BW$.t'int",
        ) if let box [Term { kind: Lit(MachUnsigned(c, _)), .. }] = args => {
            return Lit(UInteger(c));
        }
        Some(
            "prelude.int.Int8$BW$.to_int"
            | "prelude.int.Int16$BW$.to_int"
            | "prelude.int.Int32$BW$.to_int"
            | "prelude.int.Int64$BW$.to_int"
            | "prelude.int.Int128$BW$.to_int",
        ) if let box [Term { kind: Lit(MachSigned(c, _)), .. }] = args => return Lit(Integer(c)),
        _ => (),
    }

    return Call { id, subst, args };
}
