use super::{
    term::lower_pure,
    ty::{translate_ty, ty_params},
    CloneSummary, Dependencies, TransId, Why3Generator,
};
use crate::{
    ctx::*,
    translation::{
        pearlite::{Pattern, Term, TermKind},
        traits,
    },
    util,
};
use indexmap::IndexSet;
use rustc_ast::Mutability;
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{GenericArg, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Symbol, DUMMY_SP};
use why3::{
    declaration::{Axiom, Decl, TyDecl},
    exp::{Exp, Trigger},
    Ident,
};

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, TypeVisitable, TypeFoldable)]
pub(crate) enum TyInvKind {
    Trivial,
    Borrow(Mutability),
    Box,
    Adt(DefId),
    Tuple(usize),
    Slice,
}

impl TyInvKind {
    pub(crate) fn from_ty(tcx: TyCtxt<'_>, ty: Ty) -> Option<Self> {
        match ty.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
                Some(TyInvKind::Trivial)
            }
            TyKind::Ref(_, _, m) => Some(TyInvKind::Borrow(*m)),
            TyKind::Adt(adt_def, _) if adt_def.is_box() => Some(TyInvKind::Box),
            TyKind::Adt(adt_def, _) => {
                if let Some(builtin) = util::get_builtin(tcx, adt_def.did()) {
                    match builtin.as_str() {
                        "seq.Seq.seq" => Some(TyInvKind::Slice),
                        _ => Some(TyInvKind::Adt(adt_def.did())),
                    }
                } else {
                    Some(TyInvKind::Adt(adt_def.did()))
                }
            }
            TyKind::Tuple(tys) => Some(TyInvKind::Tuple(tys.len())),
            TyKind::Slice(_) => Some(TyInvKind::Slice),
            _ => None, // TODO
        }
    }

    pub(crate) fn to_skeleton_ty<'tcx>(self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        let param = Ty::new_param(tcx, 0, Symbol::intern("T"));
        match self {
            TyInvKind::Trivial => param,
            TyInvKind::Borrow(Mutability::Not) => {
                Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, param)
            }
            TyInvKind::Borrow(Mutability::Mut) => {
                Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, param)
            }
            TyInvKind::Box => Ty::new_box(tcx, param),
            TyInvKind::Adt(did) => tcx.type_of(did).instantiate_identity(),
            TyInvKind::Tuple(arity) => Ty::new_tup_from_iter(
                tcx,
                (0..arity).map(|i| Ty::new_param(tcx, i as _, Symbol::intern(&format!("T{i}")))),
            ),
            TyInvKind::Slice => Ty::new_slice(tcx, param),
        }
    }

    pub(crate) fn generics(self, ctx: &mut Why3Generator) -> Vec<Ident> {
        match self {
            TyInvKind::Trivial | TyInvKind::Borrow(_) | TyInvKind::Box | TyInvKind::Slice => {
                vec!["t".into()]
            }
            TyInvKind::Adt(def_id) => ty_params(ctx, def_id).collect(),
            TyInvKind::Tuple(arity) => (0..arity).map(|i| format!["t{i}"].into()).collect(),
        }
    }

    pub(crate) fn tyinv_substs<'tcx>(
        self,
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
    ) -> GenericArgsRef<'tcx> {
        match (self, ty.kind()) {
            (TyInvKind::Trivial, _) => tcx.mk_args(&[GenericArg::from(ty)]),
            (TyInvKind::Borrow(_), TyKind::Ref(_, ty, _))
            | (TyInvKind::Slice, TyKind::Slice(ty)) => tcx.mk_args(&[GenericArg::from(*ty)]),
            (TyInvKind::Box, TyKind::Adt(_, adt_substs)) => tcx.mk_args(&adt_substs[..1]),
            (TyInvKind::Adt(_), TyKind::Adt(_, adt_substs)) => adt_substs,
            (TyInvKind::Tuple(_), TyKind::Tuple(tys)) => {
                tcx.mk_args_from_iter(tys.iter().map(GenericArg::from))
            }
            (TyInvKind::Slice, TyKind::Adt(_, subst)) => subst,
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
            .map(|(uinv_did, _)| util::is_structural_ty_inv(tcx, uinv_did));

        // IF there is a user invariant AND it is not structural
        // OR ty is a param or alias AND we default to considering them trivial
        if user_inv == Some(false)
            || (!param_is_trivial && matches!(ty.kind(), TyKind::Param(_) | TyKind::Alias(_, _)))
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
        kind: Option<TyInvKind>,
    ) -> Term<'tcx> {
        let subject = Term::var(Symbol::intern("x"), ty);

        let term = self.inv_rhs(ctx, ty, kind);

        let inv_id = ctx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = ctx.mk_args(&[GenericArg::from(subject.ty)]);

        let lhs = Term::call(ctx.tcx, inv_id, subst, vec![subject]);

        Term::forall(Term::eq(ctx.tcx, lhs, term), (Symbol::intern("x"), ty))
    }

    fn structural_invariant(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        term: Term<'tcx>,
        inv_kind: Option<TyInvKind>,
    ) -> Term<'tcx> {
        let tcx = ctx.tcx;
        let Some(inv_kind) = inv_kind else {
            return self.mk_inv_call(ctx, term);
        };

        match inv_kind {
            TyInvKind::Trivial => Term::mk_true(tcx),
            TyInvKind::Borrow(Mutability::Not) => self.mk_inv_call(ctx, term.cur()),
            TyInvKind::Borrow(Mutability::Mut) => {
                self.mk_inv_call(ctx, term.clone().cur()).conj(self.mk_inv_call(ctx, term.fin()))
            }
            TyInvKind::Box => self.mk_inv_call(ctx, term.cur()),
            TyInvKind::Adt(_) => {
                self.build_inv_term_adt(ctx, term).unwrap_or_else(|| Term::mk_true(ctx.tcx))
            }
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
            TyInvKind::Slice => self.build_inv_term_seq(ctx, term),
        }
    }

    fn inv_rhs(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        ty: Ty<'tcx>,
        kind: Option<TyInvKind>,
    ) -> Term<'tcx> {
        if let Some(TyInvKind::Trivial) = kind {
            return Term::mk_true(ctx.tcx);
        }

        let subject = Term::var(Symbol::intern("x"), ty);

        // eprintln!("searching for {ty:?} in {param_env:?}");
        let user_inv: Option<Term<'_>> =
            resolve_user_inv(ctx.tcx, ty, self.param_env).map(|(uinv_did, uinv_subst)| {
                Term::call(ctx.tcx, uinv_did, uinv_subst, vec![subject.clone()])
            });

        // eprintln!("user inv of {kind:?} is {user_inv:?}");

        let struct_inv = self.structural_invariant(ctx, subject, kind);

        match user_inv {
            Some(inv) => inv.conj(struct_inv),
            _ => struct_inv,
        }
    }

    // TODO: Use a param env to determine whether this specific invaraint call should ne trivial
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

    fn build_inv_term_adt(
        &self,
        ctx: &mut Why3Generator<'tcx>,
        term: Term<'tcx>,
    ) -> Option<Term<'tcx>> {
        let TyKind::Adt(adt_def, subst) = term.ty.kind() else {
            unreachable!("asked to build ADT invariant for non-ADT type {:?}", term.ty)
        };

        use crate::pearlite::*;
        // trusted types are opaque and thus have no structual invariant
        if util::is_trusted(ctx.tcx, adt_def.did()) {
            return None;
        }

        let mut arms: Vec<(_, Term<'tcx>)> = vec![];

        for (var_idx, var_def) in adt_def.variants().iter().enumerate() {
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
                Pattern::Constructor {
                    adt: var_def.def_id,
                    substs: subst,
                    variant: var_idx.into(),
                    fields: pats,
                },
                exp,
            ));
        }
        let exp = {
            let self_ = term;
            Term {
                kind: TermKind::Match { scrutinee: Box::new(self_), arms },
                ty: ctx.types.bool,
                span: DUMMY_SP,
            }
        };

        Some(exp)
    }

    fn build_inv_term_seq(&self, ctx: &mut Why3Generator<'tcx>, term: Term<'tcx>) -> Term<'tcx> {
        let elt_ty;
        let seq_len;
        let seq_get;
        let int_ty;

        match term.ty.kind() {
            TyKind::Slice(ty) => {
                seq_len = ctx.get_diagnostic_item(Symbol::intern("slice_len_logic")).unwrap();
                seq_get = ctx.get_diagnostic_item(Symbol::intern("slice_index_logic")).unwrap();
                int_ty = ctx.types.u64;

                elt_ty = *ty;
            }
            TyKind::Adt(_, subst) => {
                seq_len = ctx.get_diagnostic_item(Symbol::intern("seq_len")).unwrap();
                seq_get = ctx.get_diagnostic_item(Symbol::intern("seq_index")).unwrap();

                let int_id = ctx.get_diagnostic_item(Symbol::intern("creusot_int")).unwrap();
                int_ty = ctx.type_of(int_id).skip_binder();
                elt_ty = subst.type_at(0);
            }
            _ => unreachable!("asked to build Seq invariant for non-Seq type"),
        };

        let index = Term::var(Symbol::intern("i"), int_ty);

        let subst = ctx.mk_args(&[GenericArg::from(elt_ty)]);

        let mut index_call = Term::call(ctx.tcx, seq_get, subst, vec![term.clone(), index.clone()]);
        index_call.ty = elt_ty;
        let call_term = self.mk_inv_call(ctx, index_call);

        let lower_bound = Term {
            kind: TermKind::Binary {
                op: crate::translation::pearlite::BinOp::Le,
                lhs: Box::new(Term::int(ctx.tcx, 0)),
                rhs: Box::new(index.clone()),
            },
            ty: ctx.types.bool,
            span: DUMMY_SP,
        };

        let len = Term::call(ctx.tcx, seq_len, subst, vec![term.clone()]);

        let upper_bound = Term {
            kind: TermKind::Binary {
                op: crate::translation::pearlite::BinOp::Lt,
                rhs: Box::new(len),
                lhs: Box::new(index.clone()),
            },
            ty: ctx.types.bool,
            span: DUMMY_SP,
        };

        lower_bound.implies(upper_bound).implies(call_term).forall((Symbol::intern("i"), int_ty))
    }
}

pub(crate) fn build_inv_module<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    inv_kind: TyInvKind,
) -> CloneSummary<'tcx> {
    let mut names = Dependencies::new(ctx.tcx, [TransId::TyInv(inv_kind)]);
    let generics = inv_kind.generics(ctx);
    let inv_axiom =
        names.with_vis(CloneLevel::Contract, |names| build_inv_axiom(ctx, names, inv_kind));

    {
        let param_env =
            if let TyInvKind::Adt(did) = inv_kind { ctx.param_env(did) } else { ParamEnv::empty() };

        let ty = inv_kind.to_skeleton_ty(ctx.tcx);
        if let Some((id, subst)) =
            resolve_user_inv(ctx.tcx, ty, param_env).or(user_inv_item(ctx.tcx, ty))
        {
            names.value(id, subst);
        }
    }

    let mut decls = vec![];
    decls.extend(
        generics
            .into_iter()
            .map(|ty_name| Decl::TyDecl(TyDecl::Opaque { ty_name, ty_params: vec![] })),
    );

    let (clones, summary) = names.provide_deps(ctx, GraphDepth::Shallow);
    // eprintln!("summary of {inv_kind:?} -> {summary:#?}");
    decls.extend(clones);

    decls.push(Decl::Axiom(inv_axiom));

    summary
}

fn axiom_name(ctx: &Why3Generator<'_>, inv_kind: TyInvKind) -> Ident {
    match inv_kind {
        TyInvKind::Trivial => "inv_trivial".into(),
        TyInvKind::Borrow(Mutability::Not) => "inv_borrow_shared".into(),
        TyInvKind::Borrow(Mutability::Mut) => "inv_borrow".into(),
        TyInvKind::Box => "inv_box".into(),
        TyInvKind::Adt(did) => {
            let ty_name = util::item_name(ctx.tcx, did, Namespace::TypeNS);
            format!("inv_{}", &*ty_name).into()
        }
        TyInvKind::Tuple(arity) => format!("inv_tuple{arity}").into(),
        TyInvKind::Slice => "inv_slice".into(),
    }
}

fn build_inv_axiom<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    inv_kind: TyInvKind,
) -> Axiom {
    let name = axiom_name(ctx, inv_kind);

    let param_env =
        if let TyInvKind::Adt(did) = inv_kind { ctx.param_env(did) } else { ParamEnv::empty() };

    let ty = inv_kind.to_skeleton_ty(ctx.tcx);
    let kind = TyInvKind::from_ty(ctx.tcx, ty);
    // TODO : Refactor and push binding down
    let lhs: Exp = Exp::qvar(names.ty_inv(ty)).app_to(Exp::var("x"));
    let rhs = if TyInvKind::Trivial == inv_kind {
        Exp::mk_true()
    } else {
        let inv_term = InvariantElaborator::new(param_env, false).elaborate_inv(ctx, ty, kind);
        let inv_term = lower_pure(ctx, names, &inv_term);
        inv_term
    };
    let trivial = rhs.is_true();
    let trigger =
        if ctx.opts.simple_triggers { Trigger::single(lhs.clone()) } else { Trigger::NONE };

    let axiom = Exp::forall_trig(
        vec![("x".into(), translate_ty(ctx, names, DUMMY_SP, ty))],
        trigger,
        lhs.eq(rhs),
    );
    Axiom { name, rewrite: !trivial, axiom }
}

// TODO: Handle missing defid gracefully
fn user_inv_item<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let trait_did = tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_user"))?;

    Some((trait_did, tcx.mk_args(&[GenericArg::from(ty)])))
}

fn resolve_user_inv<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let (trait_did, subst) = user_inv_item(tcx, ty)?;

    // eprintln!("resolving inv for {ty}, {param_env:?}");
    let (impl_did, subst) = traits::resolve_assoc_item_opt(tcx, param_env, trait_did, subst)?;
    let subst = tcx.try_normalize_erasing_regions(param_env, subst).unwrap_or(subst);

    // if inv resolved to the default impl and is not specializable, ignore
    if impl_did == trait_did && !traits::still_specializable(tcx, param_env, impl_did, subst) {
        None
    } else {
        Some((impl_did, subst))
    }
}
