use super::Why3Generator;
use crate::{
    contracts_items::{
        get_inv_function, get_invariant_method, is_ignore_structural_inv, is_trusted,
        is_tyinv_trivial_if_param_trivial,
    },
    pearlite::Trigger,
    traits::TraitResolved,
    translation::{
        pearlite::{Pattern, Term, TermKind},
        traits,
    },
};
use rustc_middle::ty::{GenericArg, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Symbol, DUMMY_SP};
use std::collections::HashSet;

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
        if let TraitResolved::Instance(uinv_did, _) = user_inv
            && !is_tyinv_trivial_if_param_trivial(tcx, uinv_did)
        {
            return false;
        }

        match ty.kind() {
            TyKind::Ref(_, ty, _) | TyKind::Slice(ty) | TyKind::Array(ty, _) => stack.push(*ty),
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(_, substs) if matches!(user_inv, TraitResolved::Instance(_, _)) => {
                // => The instance is annotated with tyinv_trivial_if_param_trivial
                stack.extend(substs.types())
            }
            TyKind::Adt(def, substs) => {
                if is_trusted(tcx, def.did()) {
                    continue;
                }

                if let TraitResolved::Instance(uinv_did, _) = user_inv
                    && is_ignore_structural_inv(tcx, uinv_did)
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
        let inv_id = get_inv_function(self.ctx.tcx);
        let subst = self.ctx.mk_args(&[GenericArg::from(subject.ty)]);
        let lhs = Term::call(self.ctx.tcx, self.param_env, inv_id, subst, vec![subject.clone()]);
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
            TraitResolved::Instance(uinv_did, uinv_subst) => {
                rhs = rhs.conj(Term::call(
                    self.ctx.tcx,
                    self.param_env,
                    uinv_did,
                    uinv_subst,
                    vec![subject.clone()],
                ))
            }
            TraitResolved::UnknownNotFound if !for_deps => use_imples = true,
            TraitResolved::NoInstance => (),
            _ => {
                let trait_item_did = get_invariant_method(self.ctx.tcx);
                let subst = self.ctx.tcx.mk_args(&[GenericArg::from(ty)]);
                rhs = rhs.conj(Term::call(
                    self.ctx.tcx,
                    self.param_env,
                    trait_item_did,
                    subst,
                    vec![subject.clone()],
                ))
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
        if let TraitResolved::Instance(uinv_did, _) =
            resolve_user_inv(self.ctx.tcx, ty, self.param_env)
            && is_ignore_structural_inv(self.ctx.tcx, uinv_did)
        {
            return Term::mk_true(self.ctx.tcx);
        }

        match ty.kind() {
            TyKind::Adt(adt_def, _) => {
                let adt_did = adt_def.did();
                if is_trusted(self.ctx.tcx, adt_did) {
                    Term::mk_true(self.ctx.tcx)
                } else {
                    self.build_inv_term_adt(term)
                }
            }
            TyKind::Tuple(tys) => {
                let ids: Vec<_> =
                    (0..tys.len()).map(|i| Symbol::intern(&format!("x{i}"))).collect();
                let body = Box::new(
                    ids.iter().zip(*tys).fold(Term::mk_true(self.ctx.tcx), |acc, (&id, ty)| {
                        acc.conj(self.mk_inv_call(Term::var(id, ty)))
                    }),
                );
                let pattern = Pattern::Tuple(ids.into_iter().map(Pattern::Binder).collect());
                Term {
                    kind: TermKind::Let { pattern, arg: Box::new(term), body },
                    ty: self.ctx.types.bool,
                    span: DUMMY_SP,
                }
            }
            TyKind::Closure(clos_did, substs) => {
                let tys = substs.as_closure().upvar_tys();
                let ids: Vec<_> =
                    (0..tys.len()).map(|i| Symbol::intern(&format!("x{i}"))).collect();

                let body = Box::new(
                    ids.iter().zip(tys).fold(Term::mk_true(self.ctx.tcx), |acc, (&id, ty)| {
                        acc.conj(self.mk_inv_call(Term::var(id, ty)))
                    }),
                );
                let pattern = Pattern::Constructor {
                    variant: *clos_did,
                    substs,
                    fields: ids.into_iter().map(Pattern::Binder).collect(),
                };
                Term {
                    kind: TermKind::Let { pattern, arg: Box::new(term), body },
                    ty: self.ctx.types.bool,
                    span: DUMMY_SP,
                }
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn mk_inv_call(&mut self, term: Term<'tcx>) -> Term<'tcx> {
        if let Some((inv_id, subst)) = self.ctx.type_invariant(self.param_env, term.ty) {
            Term::call(self.ctx.tcx, self.param_env, inv_id, subst, vec![term])
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

fn resolve_user_inv<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> traits::TraitResolved<'tcx> {
    let trait_item_did = get_invariant_method(tcx);
    let subst = tcx.mk_args(&[GenericArg::from(ty)]);

    traits::TraitResolved::resolve_item(tcx, param_env, trait_item_did, subst)
}
