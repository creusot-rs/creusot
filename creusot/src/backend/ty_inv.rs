use super::Why3Generator;
use crate::{
    contracts_items::{
        get_inv_function, get_invariant_method, is_ignore_structural_inv, is_trusted,
        is_tyinv_trivial_if_param_trivial,
    },
    naming::variable_name,
    translation::{
        pearlite::{Ident, Literal, Pattern, Term, TermKind, Trigger},
        traits::TraitResolved,
    },
};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_middle::ty::{GenericArg, Ty, TyCtxt, TyKind, TypingEnv};
use rustc_span::Span;
use std::collections::HashSet;

/// # Errors
///
/// This will error (and stop the compilation) if an unsupported type is
/// encountered.
///
/// # Parameters
///
/// - `span`: used for error message
pub(crate) fn is_tyinv_trivial<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    span: Span,
) -> bool {
    // we cannot use a TypeWalker as it does not visit ADT field types
    let mut visited_tys = HashSet::new();
    let mut stack = vec![ty];
    while let Some(ty) = stack.pop() {
        if !visited_tys.insert(ty) {
            continue;
        }

        let user_inv = resolve_user_inv(tcx, ty, typing_env);
        match user_inv {
            TraitResolved::NotATraitItem => unreachable!(),
            TraitResolved::NoInstance => (),
            TraitResolved::Instance { def: (uinv_did, _), .. }
                if is_tyinv_trivial_if_param_trivial(tcx, uinv_did) => {}
            _ => return false,
        }

        match ty.kind() {
            TyKind::Ref(_, ty, _) | TyKind::Slice(ty) | TyKind::Array(ty, _) => stack.push(*ty),
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(def, substs) if matches!(user_inv, TraitResolved::NoInstance) => {
                if is_trusted(tcx, def.did()) {
                    continue;
                }

                if def.is_enum() && def.variants().is_empty() {
                    return false;
                }

                stack.extend(def.all_fields().map(|f| f.ty(tcx, substs)))
            }

            // The instance is annotated with tyinv_trivial_if_param_trivial
            TyKind::Adt(_, substs) => stack.extend(substs.types()),

            TyKind::Closure(_, subst) => stack.extend(subst.as_closure().upvar_tys()),
            TyKind::Never | TyKind::Param(_) | TyKind::Alias(_, _) => return false,
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::FnDef(_, _)
            | TyKind::FnPtr(..)
            | TyKind::RawPtr(_, _)
            | TyKind::Dynamic(_, _, _) => (),
            _ => tcx.dcx().span_fatal(span, format!("Unsupported type: {ty}")),
        }
    }
    true
}

pub struct InvariantElaborator<'a, 'tcx> {
    typing_env: TypingEnv<'tcx>,
    ctx: &'a Why3Generator<'tcx>,
    pub rewrite: bool,
}

impl<'a, 'tcx> InvariantElaborator<'a, 'tcx> {
    pub(crate) fn new(typing_env: TypingEnv<'tcx>, ctx: &'a Why3Generator<'tcx>) -> Self {
        InvariantElaborator { typing_env, ctx, rewrite: false }
    }

    /// `span` is used for diagnostics.
    pub(crate) fn elaborate_inv(&mut self, ty: Ty<'tcx>, span: Span) -> Option<Term<'tcx>> {
        let x_ident = Ident::fresh_local("x").into();
        let subject = Term::var(x_ident, ty);
        let inv_id = get_inv_function(self.ctx.tcx);
        let subst = self.ctx.mk_args(&[GenericArg::from(subject.ty)]);
        let lhs = Term::call(self.ctx.tcx, self.typing_env, inv_id, subst, [subject.clone()]);
        let trig = Box::new([Trigger(Box::new([lhs.clone()]))]);

        if is_tyinv_trivial(self.ctx.tcx, self.typing_env, ty, span) {
            self.rewrite = true;
            return Some(
                lhs.eq(self.ctx.tcx, Term::true_(self.ctx.tcx)).forall_trig((x_ident, ty), trig),
            );
        }

        let mut use_imples = false;

        let mut rhs = Term::true_(self.ctx.tcx);

        match resolve_user_inv(self.ctx.tcx, ty, self.typing_env) {
            TraitResolved::NotATraitItem => unreachable!(),
            TraitResolved::Instance { def, .. } => {
                rhs = rhs.conj(Term::call(
                    self.ctx.tcx,
                    self.typing_env,
                    def.0,
                    def.1,
                    [subject.clone()],
                ))
            }
            TraitResolved::UnknownFound => {
                let trait_item_did = get_invariant_method(self.ctx.tcx);
                let subst = self.ctx.tcx.mk_args(&[GenericArg::from(ty)]);
                rhs = rhs.conj(Term::call(
                    self.ctx.tcx,
                    self.typing_env,
                    trait_item_did,
                    subst,
                    [subject.clone()],
                ))
            }
            TraitResolved::UnknownNotFound => use_imples = true,
            TraitResolved::NoInstance => (),
        }

        if matches!(ty.kind(), TyKind::Alias(..) | TyKind::Param(_)) {
            use_imples = true
        } else {
            rhs = rhs.conj(self.structural_invariant(subject, ty))
        }

        let term = if use_imples {
            if matches!(rhs.kind, TermKind::Lit(Literal::Bool(true))) {
                return None;
            }
            Term::implies(lhs, rhs)
        } else {
            self.rewrite = true;
            lhs.eq(self.ctx.tcx, rhs)
        };

        Some(term.forall_trig((x_ident, ty), trig))
    }

    fn structural_invariant(&mut self, term: Term<'tcx>, ty: Ty<'tcx>) -> Term<'tcx> {
        if let TraitResolved::Instance { def, .. } =
            resolve_user_inv(self.ctx.tcx, ty, self.typing_env)
            && is_ignore_structural_inv(self.ctx.tcx, def.0)
        {
            return Term::true_(self.ctx.tcx);
        }

        match ty.kind() {
            TyKind::Adt(adt_def, _) => {
                let adt_did = adt_def.did();
                if is_trusted(self.ctx.tcx, adt_did) {
                    Term::true_(self.ctx.tcx)
                } else {
                    self.build_inv_term_adt(term)
                }
            }
            TyKind::Tuple(tys) => {
                let idsty: Vec<_> = tys
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| (Ident::fresh_local(format!("x{i}")), ty))
                    .collect();
                let body = idsty.iter().fold(Term::true_(self.ctx.tcx), |acc, &(id, ty)| {
                    acc.conj(self.mk_inv_call(Term::var(id, ty)))
                });
                let pattern =
                    Pattern::tuple(idsty.iter().map(|&(id, ty)| Pattern::binder(id, ty)), ty);
                Term::let_(pattern, term, body)
            }
            TyKind::Closure(_, substs) => {
                let tys = substs.as_closure().upvar_tys();
                let idsty: Vec<_> = tys
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| (FieldIdx::from(i), Ident::fresh_local(format!("x{i}")), ty))
                    .collect();

                let body = idsty.iter().fold(Term::true_(self.ctx.tcx), |acc, &(_, id, ty)| {
                    acc.conj(self.mk_inv_call(Term::var(id, ty)))
                });
                let pattern = Pattern::constructor(
                    VariantIdx::ZERO,
                    idsty.iter().map(|&(fld, id, ty)| (fld, Pattern::binder(id, ty))),
                    ty,
                );
                Term::let_(pattern, term, body)
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn mk_inv_call(&mut self, term: Term<'tcx>) -> Term<'tcx> {
        if let Some((inv_id, subst)) = self.ctx.type_invariant(self.typing_env, term.ty, term.span)
        {
            Term::call(self.ctx.tcx, self.typing_env, inv_id, subst, [term])
        } else {
            Term::true_(self.ctx.tcx)
        }
    }

    fn build_inv_term_adt(&mut self, term: Term<'tcx>) -> Term<'tcx> {
        let TyKind::Adt(adt_def, substs) = term.ty.kind() else {
            unreachable!("asked to build ADT invariant for non-ADT type {:?}", term.ty)
        };

        let variants = adt_def.variants();
        if variants.is_empty() {
            return Term::false_(self.ctx.tcx);
        }
        let ty = term.ty;
        let arms = variants.iter_enumerated().map(|(var_idx, var_def)| {
            let tuple_var = var_def.ctor.is_some();

            let mut exp = Some(Term::true_(self.ctx.tcx));
            let fields = var_def.fields.iter().enumerate().map(|(field_idx, field_def)| {
                let field_name = if tuple_var {
                    Ident::fresh_local(format!("a_{field_idx}"))
                } else {
                    Ident::fresh_local(variable_name(field_def.ident(self.ctx.tcx).name.as_str()))
                };

                let field_ty = field_def.ty(self.ctx.tcx, substs);

                let f_exp = self.mk_inv_call(Term::var(field_name, field_ty));
                exp = Some(exp.take().unwrap().conj(f_exp));
                (field_idx.into(), Pattern::binder(field_name, field_ty))
            });

            (Pattern::constructor(var_idx, fields, ty), exp.unwrap())
        });
        term.match_(arms)
    }
}

fn resolve_user_inv<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    typing_env: TypingEnv<'tcx>,
) -> TraitResolved<'tcx> {
    TraitResolved::resolve_item(
        tcx,
        typing_env,
        get_invariant_method(tcx),
        tcx.mk_args(&[GenericArg::from(ty)]),
    )
}
