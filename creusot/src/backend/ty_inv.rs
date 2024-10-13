use super::{term::lower_pure, CloneSummary, Dependencies, TransId, Why3Generator};
use crate::{
    ctx::*,
    pearlite::Trigger,
    traits::TraitResol,
    translation::{
        pearlite::{Pattern, Term, TermKind},
        traits,
    },
    util::{self},
};
use rustc_middle::ty::{GenericArg, GenericArgs, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Symbol, DUMMY_SP};
use std::{collections::HashSet, iter};

// Rewrite a type as a "head type" and a ssusbtitution, such that the head type applied to the substitution
// equals the type.
// The head type is used as a dependency node.
pub(crate) fn tyinv_head_and_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> (Ty<'tcx>, GenericArgsRef<'tcx>) {
    let def = || {
        // Return value to use if there is no structural invariant
        (
            Ty::new_param(tcx, 0, Symbol::intern(&format!("T"))),
            tcx.mk_args_from_iter(iter::once(GenericArg::from(ty))),
        )
    };

    if let TraitResol::Instance(uinv_did, _) = resolve_user_inv(tcx, ty, param_env)
        && util::is_ignore_structural_inv(tcx, uinv_did)
    {
        return def();
    }

    if is_tyinv_trivial(tcx, param_env, ty) {
        return def();
    }

    match ty.kind() {
        TyKind::Adt(adt_def, subst) => {
            (Ty::new_adt(tcx, *adt_def, GenericArgs::identity_for_item(tcx, adt_def.did())), subst)
        }
        TyKind::Closure(did, _) => (ty, GenericArgs::identity_for_item(tcx, tcx.parent(*did))),
        TyKind::Tuple(tys) => {
            let params = (0..tys.len())
                .map(|i| Ty::new_param(tcx, i as _, Symbol::intern(&format!("T{i}"))));
            let tup = Ty::new_tup_from_iter(tcx, params);
            let subst = tcx.mk_args_from_iter(tys.iter().map(GenericArg::from));
            (tup, subst)
        }
        TyKind::Alias(..) | TyKind::Param(_) => def(),
        _ => unimplemented!("{ty:?}"), // TODO
    }
}

pub(crate) fn is_tyinv_trivial<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    // we cannot use a TypeWalker as it does not visit ADT field types
    let mut visited_tys = HashSet::new();
    let mut stack = vec![ty];
    while let Some(ty) = stack.pop() {
        if !visited_tys.insert(ty.clone()) {
            continue;
        }

        let user_inv = resolve_user_inv(tcx, ty, param_env);
        if let TraitResol::Instance(uinv_did, _) = user_inv
            && !util::is_tyinv_trivial_if_param_trivial(tcx, uinv_did)
        {
            return false;
        }

        match ty.kind() {
            TyKind::Ref(_, ty, _) | TyKind::Slice(ty) | TyKind::Array(ty, _) => stack.push(*ty),
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(_, substs) if matches!(user_inv, TraitResol::Instance(_, _)) => {
                // => The instance is annotated with tyinv_trivial_if_param_trivial
                stack.extend(substs.types())
            }
            TyKind::Adt(def, substs) => {
                if util::is_trusted(tcx, def.did()) {
                    continue;
                }

                if let TraitResol::Instance(uinv_did, _) = user_inv
                    && util::is_ignore_structural_inv(tcx, uinv_did)
                {
                    continue;
                }

                stack.extend(def.all_fields().map(|f| f.ty(tcx, substs)))
            }
            TyKind::Closure(_, subst) => stack.extend(subst.as_closure().upvar_tys()),
            TyKind::Never | TyKind::Param(_) | TyKind::Alias(_, _) => return false,
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::FnDef(_, _)
            | TyKind::FnPtr(_)
            | TyKind::RawPtr(_, _) => (),
            _ => unimplemented!("{ty:?}"),
        }
    }
    true
}

pub struct InvariantElaborator<'a, 'tcx> {
    param_env: ParamEnv<'tcx>,
    ctx: &'a mut Why3Generator<'tcx>,
    pub rewrite: bool,
}

impl<'a, 'tcx> InvariantElaborator<'a, 'tcx> {
    pub(crate) fn new(param_env: ParamEnv<'tcx>, ctx: &'a mut Why3Generator<'tcx>) -> Self {
        InvariantElaborator { param_env, ctx, rewrite: false }
    }

    pub(crate) fn elaborate_inv(&mut self, ty: Ty<'tcx>, for_deps: bool) -> Option<Term<'tcx>> {
        let subject = Term::var(Symbol::intern("x"), ty);
        let inv_id =
            self.ctx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = self.ctx.mk_args(&[GenericArg::from(subject.ty)]);
        let lhs = Term::call(self.ctx.tcx, inv_id, subst, vec![subject.clone()]);
        let trig = vec![Trigger(vec![lhs.clone()])];

        if is_tyinv_trivial(self.ctx.tcx, self.param_env, ty) {
            self.rewrite = true;
            return Some(Term::eq(self.ctx.tcx, lhs, Term::mk_true(self.ctx.tcx)).forall_trig(
                self.ctx.tcx,
                (Symbol::intern("x"), ty),
                trig,
            ));
        }

        let mut use_imples = false;

        matches!(ty.kind(), TyKind::Alias(..) | TyKind::Param(_));

        let mut rhs = Term::mk_true(self.ctx.tcx);

        match resolve_user_inv(self.ctx.tcx, ty, self.param_env) {
            TraitResol::Instance(uinv_did, uinv_subst) => {
                rhs =
                    rhs.conj(Term::call(self.ctx.tcx, uinv_did, uinv_subst, vec![subject.clone()]))
            }
            TraitResol::UnknownNotFound if !for_deps => use_imples = true,
            TraitResol::NoInstance => (),
            _ => {
                let trait_item_did = self
                    .ctx
                    .tcx
                    .get_diagnostic_item(Symbol::intern("creusot_invariant_user"))
                    .unwrap();
                let subst = self.ctx.tcx.mk_args(&[GenericArg::from(ty)]);
                rhs =
                    rhs.conj(Term::call(self.ctx.tcx, trait_item_did, subst, vec![subject.clone()]))
            }
        }

        if matches!(ty.kind(), TyKind::Alias(..) | TyKind::Param(_)) {
            use_imples = true
        } else {
            rhs = rhs.conj(self.structural_invariant(subject, ty))
        }

        let term = if use_imples {
            if matches!(rhs.kind, TermKind::Lit(crate::pearlite::Literal::Bool(true))) {
                return None;
            }
            Term::implies(lhs, rhs)
        } else {
            self.rewrite = true;
            Term::eq(self.ctx.tcx, lhs, rhs)
        };

        Some(term.forall_trig(self.ctx.tcx, (Symbol::intern("x"), ty), trig))
    }

    fn structural_invariant(&mut self, term: Term<'tcx>, ty: Ty<'tcx>) -> Term<'tcx> {
        if let TraitResol::Instance(uinv_did, _) =
            resolve_user_inv(self.ctx.tcx, ty, self.param_env)
            && util::is_ignore_structural_inv(self.ctx.tcx, uinv_did)
        {
            return Term::mk_true(self.ctx.tcx);
        }

        match ty.kind() {
            TyKind::Adt(adt_def, _) => {
                let adt_did = adt_def.did();
                if util::is_trusted(self.ctx.tcx, adt_did) {
                    Term::mk_true(self.ctx.tcx)
                } else {
                    self.build_inv_term_adt(term)
                }
            }
            TyKind::Tuple(tys) => {
                let ids = ('a'..).take(tys.len());

                let pattern = Pattern::Tuple(
                    ids.clone()
                        .into_iter()
                        .map(|id| Symbol::intern(&id.to_string()))
                        .map(Pattern::Binder)
                        .collect(),
                );
                Term {
                    kind: TermKind::Let {
                        pattern,
                        arg: Box::new(term),
                        body: Box::new(ids.into_iter().enumerate().fold(
                            Term::mk_true(self.ctx.tcx),
                            |acc, (ix, id)| {
                                acc.conj(self.mk_inv_call(Term::var(
                                    Symbol::intern(&id.to_string()),
                                    tys[ix],
                                )))
                            },
                        )),
                    },
                    ty: self.ctx.types.bool,
                    span: DUMMY_SP,
                }
            }
            TyKind::Closure(clos_did, substs) => {
                let tys = substs.as_closure().upvar_tys();
                let ids = ('a'..).take(tys.len());

                let pattern = Pattern::Constructor {
                    variant: *clos_did,
                    substs,
                    fields: ids
                        .clone()
                        .into_iter()
                        .map(|id| Symbol::intern(&id.to_string()))
                        .map(Pattern::Binder)
                        .collect(),
                };
                Term {
                    kind: TermKind::Let {
                        pattern,
                        arg: Box::new(term),
                        body: Box::new(ids.into_iter().enumerate().fold(
                            Term::mk_true(self.ctx.tcx),
                            |acc, (ix, id)| {
                                acc.conj(self.mk_inv_call(Term::var(
                                    Symbol::intern(&id.to_string()),
                                    tys[ix],
                                )))
                            },
                        )),
                    },
                    ty: self.ctx.types.bool,
                    span: DUMMY_SP,
                }
            }
            _ => unimplemented!("{ty:?}"), // TODO
        }
    }

    pub(crate) fn mk_inv_call(&mut self, term: Term<'tcx>) -> Term<'tcx> {
        if let Some((inv_id, subst)) = self.ctx.type_invariant(self.param_env, term.ty) {
            Term::call(self.ctx.tcx, inv_id, subst, vec![term])
        } else {
            Term::mk_true(self.ctx.tcx)
        }
    }

    fn build_inv_term_adt(&mut self, term: Term<'tcx>) -> Term<'tcx> {
        let TyKind::Adt(adt_def, subst) = term.ty.kind() else {
            unreachable!("asked to build ADT invariant for non-ADT type {:?}", term.ty)
        };

        use crate::pearlite::*;

        let mut arms: Vec<(_, Term<'tcx>)> = vec![];

        for var_def in adt_def.variants() {
            let tuple_var = var_def.ctor.is_some();

            let mut pats: Vec<Pattern<'tcx>> = vec![];
            let mut exp: Term<'tcx> = Term::mk_true(self.ctx.tcx);
            for (field_idx, field_def) in var_def.fields.iter().enumerate() {
                let field_name: Symbol = if tuple_var {
                    Symbol::intern(&format!("a_{field_idx}"))
                } else {
                    field_def.name
                };

                let field_ty = field_def.ty(self.ctx.tcx, subst);

                let var = Term::var(field_name, field_ty);
                let f_exp = self.mk_inv_call(var);
                exp = exp.conj(f_exp);
                pats.push(Pattern::Binder(field_name));
            }

            arms.push((
                Pattern::Constructor { variant: var_def.def_id, substs: subst, fields: pats },
                exp,
            ));
        }

        Term {
            kind: TermKind::Match { scrutinee: Box::new(term), arms },
            ty: self.ctx.types.bool,
            span: DUMMY_SP,
        }
    }
}

pub(crate) fn get_tyinv_deps<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> CloneSummary<'tcx> {
    let mut names = Dependencies::new(ctx.tcx, [TransId::TyInv(ty)]);

    let param_env = if let Some(adt) = ty.ty_adt_def() {
        ctx.tcx.param_env(adt.did())
    } else {
        ParamEnv::empty()
    };

    if let Some(inv_term) = InvariantElaborator::new(param_env, ctx).elaborate_inv(ty, true) {
        lower_pure(ctx, &mut names, &inv_term);
    }

    let (_, summary) = names.provide_deps(ctx, GraphDepth::Shallow);
    summary
}

fn resolve_user_inv<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> traits::TraitResol<'tcx> {
    let trait_item_did = tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_user")).unwrap();
    let subst = tcx.mk_args(&[GenericArg::from(ty)]);

    traits::resolve_assoc_item_opt(tcx, param_env, trait_item_did, subst)
}
