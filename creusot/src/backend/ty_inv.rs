use super::{term::lower_pure, CloneSummary, Dependencies, TransId, Why3Generator};
use crate::{
    ctx::*,
    translation::{
        pearlite::{Pattern, Term, TermKind},
        traits,
    },
    util::{self, ident_path},
};
use indexmap::IndexSet;
use rustc_hir::def_id::DefId;
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{GenericArg, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Symbol, DUMMY_SP};
use why3::Ident;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, TypeVisitable, TypeFoldable)]
pub(crate) enum TyInvKind {
    NotStructural,
    Trivial,
    Adt(DefId),
    Tuple(usize),
}

impl TyInvKind {
    pub(crate) fn from_ty<'tcx>(
        ty: Ty<'tcx>,
        param_env: ParamEnv<'tcx>,
        ctx: &TranslationCtx<'tcx>,
        param_is_trivial: bool,
    ) -> Self {
        if is_tyinv_trivial(ctx.tcx, param_env, ty, param_is_trivial) {
            return TyInvKind::NotStructural;
        }
        if let Some((uinv_did, _)) = resolve_user_inv(ctx.tcx, ty, param_env)
            && util::is_ignore_structural_inv(ctx.tcx, uinv_did)
        {
            return TyInvKind::NotStructural;
        }
        match ty.kind() {
            TyKind::Adt(adt_def, _) => {
                let adt_did = adt_def.did();
                if util::is_trusted(ctx.tcx, adt_did) {
                    TyInvKind::NotStructural
                } else {
                    TyInvKind::Adt(adt_did)
                }
            }
            TyKind::Tuple(tys) => TyInvKind::Tuple(tys.len()),
            _ => unimplemented!("{ty:?}"), // TODO
        }
    }

    pub(crate) fn to_skeleton_ty<'tcx>(self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            TyInvKind::NotStructural => Ty::new_param(tcx, 0, Symbol::intern("T")),
            TyInvKind::Trivial => Ty::new_param(tcx, 0, Symbol::intern("T")),
            TyInvKind::Adt(did) => tcx.type_of(did).instantiate_identity(),
            TyInvKind::Tuple(arity) => Ty::new_tup_from_iter(
                tcx,
                (0..arity).map(|i| Ty::new_param(tcx, i as _, Symbol::intern(&format!("T{i}")))),
            ),
        }
    }

    pub(crate) fn tyinv_substs<'tcx>(
        self,
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
    ) -> GenericArgsRef<'tcx> {
        match (self, ty.kind()) {
            (TyInvKind::NotStructural, _) => tcx.mk_args(&[GenericArg::from(ty)]),
            (TyInvKind::Trivial, _) => tcx.mk_args(&[GenericArg::from(ty)]),
            (TyInvKind::Adt(_), TyKind::Adt(_, adt_substs)) => adt_substs,
            (TyInvKind::Tuple(_), TyKind::Tuple(tys)) => {
                tcx.mk_args_from_iter(tys.iter().map(GenericArg::from))
            }
            a => unreachable!("{a:?}"),
        }
    }
}

pub(crate) fn is_tyinv_trivial<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
    param_is_trivial: bool,
) -> bool {
    if ty.is_closure() {
        return true;
    }

    // we cannot use a TypeWalker as it does not visit ADT field types
    let mut visited_adts = IndexSet::new();
    let mut stack = vec![ty];
    while let Some(ty) = stack.pop() {
        let user_inv = resolve_user_inv(tcx, ty, param_env)
            .map(|(uinv_did, _)| util::is_ignore_structural_inv(tcx, uinv_did));

        // IF there is a user invariant AND it is not structural
        // OR ty is a param or alias AND we default to considering them trivial
        if user_inv == Some(false)
            || (!param_is_trivial && matches!(ty.kind(), TyKind::Param(_) | TyKind::Alias(_, _)))
            || matches!(ty.kind(), TyKind::Never)
        {
            return false;
        }

        match ty.kind() {
            TyKind::Ref(_, ty, _) | TyKind::Slice(ty) => stack.push(*ty),
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(def, substs) if def.is_box() => stack.push(substs.type_at(0)),
            TyKind::Adt(def, substs)
                if util::get_builtin(tcx, def.did()).is_some() || user_inv == Some(true) =>
            {
                // if the ADT has a structural user invariant, do not look into fields but only consider substs
                stack.extend(substs.types())
            }
            TyKind::Adt(def, substs) => {
                let did = def.did();
                if util::get_builtin(tcx, did).is_none() && visited_adts.insert(did) {
                    stack.extend(def.all_fields().map(|f| f.ty(tcx, substs)))
                }
            }
            _ => {}
        }
    }
    true
}

pub struct InvariantElaborator<'tcx> {
    default_trivial: bool,
    param_env: ParamEnv<'tcx>,
}

impl<'tcx> InvariantElaborator<'tcx> {
    pub(crate) fn new(param_env: ParamEnv<'tcx>, default_trivial: bool) -> Self {
        InvariantElaborator { default_trivial, param_env }
    }

    pub(crate) fn elaborate_inv(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        ty: Ty<'tcx>,
        kind: TyInvKind,
    ) -> Term<'tcx> {
        let subject = Term::var(Symbol::intern("x"), ty);

        let rhs = self.inv_rhs(ctx, ty, kind);

        let inv_id = ctx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = ctx.mk_args(&[GenericArg::from(subject.ty)]);

        let lhs = Term::call(ctx.tcx, inv_id, subst, vec![subject]);

        Term::forall(Term::eq(ctx.tcx, lhs, rhs), ctx.tcx, (Symbol::intern("x"), ty))
    }

    fn structural_invariant(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        term: Term<'tcx>,
        inv_kind: TyInvKind,
    ) -> Term<'tcx> {
        match inv_kind {
            TyInvKind::Trivial => Term::mk_true(ctx.tcx),
            TyInvKind::NotStructural => Term::mk_true(ctx.tcx),
            TyInvKind::Adt(_) => self.build_inv_term_adt(ctx, term),
            TyInvKind::Tuple(l) => {
                let TyKind::Tuple(tys) = term.ty.kind() else { unreachable!() };

                let ids = ('a'..).take(l);

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
                            Term::mk_true(ctx.tcx),
                            |acc, (ix, id)| {
                                acc.conj(self.mk_inv_call(
                                    ctx,
                                    Term::var(Symbol::intern(&id.to_string()), tys[ix]),
                                ))
                            },
                        )),
                    },
                    ty: ctx.types.bool,
                    span: DUMMY_SP,
                }
            }
        }
    }

    fn inv_rhs(&self, ctx: &mut Why3Generator<'tcx>, ty: Ty<'tcx>, kind: TyInvKind) -> Term<'tcx> {
        if let TyInvKind::Trivial = kind {
            return Term::mk_true(ctx.tcx);
        }

        let subject = Term::var(Symbol::intern("x"), ty);

        //eprintln!("searching for {ty:?} in {:?}", self.param_env);
        let user_inv = resolve_user_inv(ctx.tcx, ty, self.param_env)
            .map(|(uinv_did, uinv_subst)| {
                Term::call(ctx.tcx, uinv_did, uinv_subst, vec![subject.clone()])
            })
            .unwrap_or(Term::mk_true(ctx.tcx));
        // eprintln!("user inv of {kind:?} is {user_inv:?}");

        let struct_inv = self.structural_invariant(ctx, subject, kind);

        user_inv.conj(struct_inv)
    }

    // TODO: Use a param env to determine whether this specific invariant call should be trivial
    // TODO: Cache the result of invariant trivial checks
    pub(crate) fn mk_inv_call(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        term: Term<'tcx>,
    ) -> Term<'tcx> {
        if is_tyinv_trivial(ctx.tcx, self.param_env, term.ty, self.default_trivial) {
            return Term::mk_true(ctx.tcx);
        }

        let inv_id = ctx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = ctx.mk_args(&[GenericArg::from(term.ty)]);
        let call_term = Term::call(ctx.tcx, inv_id, subst, vec![term]);
        call_term
    }

    fn build_inv_term_adt(&self, ctx: &mut Why3Generator<'tcx>, term: Term<'tcx>) -> Term<'tcx> {
        let TyKind::Adt(adt_def, subst) = term.ty.kind() else {
            unreachable!("asked to build ADT invariant for non-ADT type {:?}", term.ty)
        };

        use crate::pearlite::*;

        let mut arms: Vec<(_, Term<'tcx>)> = vec![];

        for var_def in adt_def.variants() {
            let tuple_var = var_def.ctor.is_some();

            let mut pats: Vec<Pattern<'tcx>> = vec![];
            let mut exp: Term<'tcx> = Term::mk_true(ctx.tcx);
            for (field_idx, field_def) in var_def.fields.iter().enumerate() {
                let field_name: Symbol = if tuple_var {
                    Symbol::intern(&format!("a_{field_idx}"))
                } else {
                    field_def.name
                };

                let field_ty = field_def.ty(ctx.tcx, subst);

                let var = Term::var(field_name, field_ty);
                let f_exp = self.mk_inv_call(ctx, var);
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
            ty: ctx.types.bool,
            span: DUMMY_SP,
        }
    }
}

pub(crate) fn inv_module_name(tcx: TyCtxt, kind: TyInvKind) -> Ident {
    match kind {
        TyInvKind::NotStructural => "TyInv_NotStructural".into(),
        TyInvKind::Trivial => "TyInv_Trivial".into(),
        TyInvKind::Adt(adt_did) => format!("{}_Inv", ident_path(tcx, adt_did)).into(),
        TyInvKind::Tuple(arity) => format!("TyInv_Tuple{arity}").into(),
    }
}

pub(crate) fn build_inv_module<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    inv_kind: TyInvKind,
) -> CloneSummary<'tcx> {
    let mut names = Dependencies::new(ctx.tcx, [TransId::TyInv(inv_kind)]);
    build_inv_axiom(ctx, &mut names, inv_kind);

    {
        let param_env =
            if let TyInvKind::Adt(did) = inv_kind { ctx.param_env(did) } else { ParamEnv::empty() };

        let ty = inv_kind.to_skeleton_ty(ctx.tcx);
        let (id, subst) =
            resolve_user_inv(ctx.tcx, ty, param_env).unwrap_or(user_inv_item(ctx.tcx, ty));
        names.value(id, subst);
    }

    let (_, summary) = names.provide_deps(ctx, GraphDepth::Shallow);
    //eprintln!("{inv_kind:?} ====> {summary:#?}\n\n");
    summary
}

fn build_inv_axiom<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    inv_kind: TyInvKind,
) {
    let param_env =
        if let TyInvKind::Adt(did) = inv_kind { ctx.param_env(did) } else { ParamEnv::empty() };

    let ty = inv_kind.to_skeleton_ty(ctx.tcx);
    let inv_term = InvariantElaborator::new(param_env, false).elaborate_inv(ctx, ty, inv_kind);
    lower_pure(ctx, names, &inv_term);
}

fn user_inv_item<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> (DefId, GenericArgsRef<'tcx>) {
    let trait_item_did = tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_user")).unwrap();
    (trait_item_did, tcx.mk_args(&[GenericArg::from(ty)]))
}

fn resolve_user_inv<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let (trait_did, subst) = user_inv_item(tcx, ty);

    // eprintln!("resolving inv for {ty}, {param_env:?}");
    let (impl_did, subst) = traits::resolve_assoc_item_opt(tcx, param_env, trait_did, subst)?;
    let subst = tcx.try_normalize_erasing_regions(param_env, subst).unwrap_or(subst);

    // if inv resolved to the default impl and is not specializable, ignore
    if impl_did == trait_did && !traits::still_specializable(tcx, param_env, trait_did, subst) {
        None
    } else {
        Some((impl_did, subst))
    }
}
