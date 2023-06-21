use super::{
    ty::{translate_ty, ty_param_names},
    CloneMap, CloneSummary, TransId, Why3Generator,
};
use crate::{ctx::*, translation::traits, util};
use indexmap::IndexSet;
use rustc_ast::Mutability;
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{subst::SubstsRef, AdtDef, GenericArg, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Symbol, DUMMY_SP};
use why3::{
    declaration::{Axiom, Decl, Module, TyDecl},
    exp::{Constant, Exp, Pattern},
    ty::Type as MlT,
    Ident, QName,
};

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) enum TyInvKind {
    Trivial,
    Borrow(Mutability),
    Box,
    Adt(DefId),
    Tuple(usize),
    Slice,
}

impl TyInvKind {
    pub(crate) fn from_ty(ty: Ty) -> Self {
        match ty.kind() {
            TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
                TyInvKind::Trivial
            }
            TyKind::Ref(_, _, m) => TyInvKind::Borrow(*m),
            TyKind::Adt(adt_def, _) if adt_def.is_box() => TyInvKind::Box,
            // TODO: if ADT inv is trivial, return TyInvKind::Trivial (optimization)
            TyKind::Adt(adt_def, _) => TyInvKind::Adt(adt_def.did()),
            TyKind::Tuple(tys) => TyInvKind::Tuple(tys.len()),
            TyKind::Slice(_) => TyInvKind::Slice,
            _ => TyInvKind::Trivial, // TODO
        }
    }

    pub(crate) fn to_skeleton_ty<'tcx>(self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        let param = tcx.mk_ty_param(0, Symbol::intern("T"));
        match self {
            TyInvKind::Trivial => param,
            TyInvKind::Borrow(Mutability::Not) => tcx.mk_imm_ref(tcx.lifetimes.re_erased, param),
            TyInvKind::Borrow(Mutability::Mut) => tcx.mk_mut_ref(tcx.lifetimes.re_erased, param),
            TyInvKind::Box => tcx.mk_box(param),
            TyInvKind::Adt(did) => tcx.type_of(did).subst_identity(),
            TyInvKind::Tuple(arity) => tcx.mk_tup_from_iter(
                (0..arity).map(|i| tcx.mk_ty_param(i as _, Symbol::intern(&format!("T{i}")))),
            ),
            TyInvKind::Slice => tcx.mk_slice(param),
        }
    }

    pub(crate) fn generics(self, tcx: TyCtxt) -> Vec<Ident> {
        match self {
            TyInvKind::Trivial | TyInvKind::Borrow(_) | TyInvKind::Box | TyInvKind::Slice => {
                vec!["t".into()]
            }
            TyInvKind::Adt(def_id) => ty_param_names(tcx, def_id).collect(),
            TyInvKind::Tuple(arity) => (0..arity).map(|i| format!["t{i}"].into()).collect(),
        }
    }
}

pub(crate) fn tyinv_substs<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> SubstsRef<'tcx> {
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
            tcx.mk_substs(&[GenericArg::from(ty)])
        }
        TyKind::Ref(_, ty, _) | TyKind::Slice(ty) => tcx.mk_substs(&[GenericArg::from(*ty)]),
        TyKind::Adt(adt_def, adt_substs) if adt_def.is_box() => tcx.mk_substs(&adt_substs[..1]),
        TyKind::Adt(_, adt_substs) => adt_substs,
        TyKind::Tuple(tys) => tcx.mk_substs_from_iter(tys.iter().map(GenericArg::from)),
        _ => tcx.mk_substs(&[GenericArg::from(ty)]),
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Mode {
    Field,
    Axiom,
}

pub(crate) fn is_tyinv_trivial<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
    default_trivial: bool,
) -> bool {
    if ty.is_closure() {
        return true;
    }

    // we cannot use a TypeWalker as it does not visit ADT field types
    let mut visited_adts = IndexSet::new();
    let mut stack = vec![ty];
    while let Some(ty) = stack.pop() {
        if resolve_user_inv(tcx, ty, param_env).is_some()
            // HACK we should never consider invariants of param types trivial 
            || (!default_trivial && matches!(ty.kind(), TyKind::Param(_)))
        {
            return false;
        }

        match ty.kind() {
            TyKind::Ref(_, ty, _) | TyKind::Slice(ty) => stack.push(*ty),
            TyKind::Tuple(tys) => stack.extend(*tys),
            TyKind::Adt(def, substs) if def.is_box() => stack.push(substs.type_at(0)),
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

pub(crate) fn build_inv_module<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    inv_kind: TyInvKind,
) -> (Module, CloneSummary<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, TransId::TyInv(inv_kind), CloneLevel::Stub);
    let generics = inv_kind.generics(ctx.tcx);
    let inv_axiom = build_inv_axiom(ctx, &mut names, inv_kind);

    let mut decls = vec![];
    decls.extend(
        generics
            .into_iter()
            .map(|ty_name| Decl::TyDecl(TyDecl::Opaque { ty_name, ty_params: vec![] })),
    );

    let (clones, summary) = names.to_clones(ctx);
    decls.extend(clones);

    decls.push(Decl::Axiom(inv_axiom));

    (Module { name: util::inv_module_name(ctx.tcx, inv_kind), decls }, summary)
}

fn build_inv_axiom<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    inv_kind: TyInvKind,
) -> Axiom {
    let name = match inv_kind {
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
    };

    let param_env =
        if let TyInvKind::Adt(did) = inv_kind { ctx.param_env(did) } else { ParamEnv::empty() };

    let ty = inv_kind.to_skeleton_ty(ctx.tcx);
    let lhs: Exp = Exp::impure_qvar(names.ty_inv(ty)).app_to(Exp::pure_var("self".into()));
    let rhs = if TyInvKind::Trivial == inv_kind {
        Exp::mk_true()
    } else {
        build_inv_exp(ctx, names, "self".into(), ty, param_env, Mode::Axiom)
            .unwrap_or_else(|| Exp::mk_true())
    };
    let trivial = rhs.is_true();

    let axiom = Exp::Forall(
        vec![("self".into(), translate_ty(ctx, names, DUMMY_SP, ty))],
        Box::new(lhs.eq(rhs)),
    );
    Axiom { name, rewrite: !trivial, axiom }
}

fn build_inv_exp<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    ident: Ident,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
    mode: Mode,
) -> Option<Exp> {
    let ty = ctx.tcx.normalize_erasing_regions(param_env, ty);

    if mode == Mode::Field && is_tyinv_trivial(ctx.tcx, param_env, ty, false) {
        return None;
    }

    let user_inv = if mode == Mode::Axiom {
        resolve_user_inv(ctx.tcx, ty, param_env).map(|(uinv_did, uinv_subst)| {
            let inv_name = names.value(uinv_did, uinv_subst);
            Exp::impure_qvar(inv_name).app(vec![Exp::pure_var(ident.clone())])
        })
    } else {
        None
    };

    let struct_inv = build_inv_exp_struct(ctx, names, ident, ty, param_env, mode);

    match (user_inv, struct_inv) {
        (None, None) => None,
        (Some(inv), None) | (None, Some(inv)) => Some(inv),
        (Some(user_inv), Some(struct_inv)) => Some(user_inv.log_and(struct_inv)),
    }
}

fn build_inv_exp_struct<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    ident: Ident,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
    mode: Mode,
) -> Option<Exp> {
    match ty.kind() {
        TyKind::Ref(_, ty, Mutability::Not) => {
            build_inv_exp(ctx, names, ident, *ty, param_env, mode)
        }
        TyKind::Ref(_, ty, Mutability::Mut) => {
            let inv = build_inv_exp(ctx, names, "a".into(), *ty, param_env, mode)?;
            names.import_prelude_module(PreludeModule::Borrow);

            let mut inv_cur = inv.clone();
            let cur = Exp::Current(Box::new(Exp::pure_var(ident.clone())));
            inv_cur.subst(&[("a".into(), cur)].into());

            let mut inv_fin = inv;
            let fin = Exp::Final(Box::new(Exp::pure_var(ident)));
            inv_fin.subst(&[("a".into(), fin)].into());

            Some(inv_cur.log_and(inv_fin))
        }
        TyKind::Tuple(tys) => {
            let fields: Vec<Ident> =
                tys.iter().enumerate().map(|(i, _)| format!("a_{i}").into()).collect();

            let body = tys
                .iter()
                .enumerate()
                .flat_map(|(i, t)| build_inv_exp(ctx, names, fields[i].clone(), t, param_env, mode))
                .reduce(|e1, e2| e1.log_and(e2))?;

            let pattern = Pattern::TupleP(fields.into_iter().map(Pattern::VarP).collect());
            Some(Exp::Let { pattern, arg: Box::new(Exp::pure_var(ident)), body: Box::new(body) })
        }
        TyKind::Slice(ty) => {
            names.import_prelude_module(PreludeModule::Slice);
            let seq = Exp::pure_qvar(QName::from_string("Slice.id").unwrap())
                .app_to(Exp::pure_var(ident));
            build_inv_exp_seq(ctx, names, seq, param_env, *ty)
        }
        TyKind::Adt(adt_def, adt_subst) if adt_def.is_box() => {
            build_inv_exp(ctx, names, ident, adt_subst.type_at(0), param_env, mode)
        }
        TyKind::Adt(adt_def, adt_subst) if util::get_builtin(ctx.tcx, adt_def.did()).is_some() => {
            match util::get_builtin(ctx.tcx, adt_def.did()).unwrap().as_str() {
                "prelude.Ghost.ghost_ty" => {
                    let mut inv = build_inv_exp(
                        ctx,
                        names,
                        "a".into(),
                        adt_subst.type_at(0),
                        param_env,
                        mode,
                    )?;
                    let inner = Exp::pure_qvar(QName::from_string("Ghost.inner").unwrap())
                        .app_to(Exp::pure_var(ident));
                    inv.subst(&[("a".into(), inner)].into());
                    Some(inv)
                }
                "seq.Seq.seq" => build_inv_exp_seq(
                    ctx,
                    names,
                    Exp::pure_var(ident),
                    param_env,
                    adt_subst.type_at(0),
                ),
                _ => None,
            }
        }
        TyKind::Adt(adt_def, subst) if mode == Mode::Axiom => {
            build_inv_exp_adt(ctx, names, ident, param_env, *adt_def, subst)
        }
        TyKind::Adt(_, _) | TyKind::Param(_) => {
            let inv_fun = Exp::impure_qvar(names.ty_inv(ty));
            Some(inv_fun.app_to(Exp::pure_var(ident)))
        }
        _ => None, // TODO add more cases
    }
}

fn build_inv_exp_seq<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    seq: Exp,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<Exp> {
    names.import_prelude_module(PreludeModule::Seq);
    names.import_prelude_module(PreludeModule::Int);

    let const_0 = Exp::Const(Constant::Int(0, None));
    let i: Exp = Exp::pure_var("i".into());
    let len = Exp::pure_qvar(QName::from_string("Seq.length").unwrap()).app_to(seq.clone());
    let bounds = const_0.leq(i.clone()).log_and(i.clone().lt(len));

    let ith = Exp::pure_qvar(QName::from_string("Seq.get").unwrap()).app(vec![seq, i]);
    let mut body = build_inv_exp(ctx, names, "a".into(), ty, param_env, Mode::Field)?;
    body.subst(&[("a".into(), ith)].into());

    Some(Exp::Forall(vec![("i".into(), MlT::Integer)], Box::new(bounds.implies(body))))
}

fn build_inv_exp_adt<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    ident: Ident,
    param_env: ParamEnv<'tcx>,
    adt_def: AdtDef,
    subst: SubstsRef<'tcx>,
) -> Option<Exp> {
    let mut branches = vec![];
    let mut trivial = true;

    for (var_idx, var_def) in adt_def.variants().iter().enumerate() {
        let tuple_var = var_def.ctor.is_some();

        let mut pats = vec![];
        let mut exp = Exp::mk_true();
        for (field_idx, field_def) in var_def.fields.iter().enumerate() {
            let field_name: Ident = if tuple_var {
                format!("a_{field_idx}").into()
            } else {
                field_def.name.as_str().into()
            };

            let field_ty = field_def.ty(ctx.tcx, subst);
            if let Some(mut field_inv) =
                build_inv_exp(ctx, names, field_name.clone(), field_ty, param_env, Mode::Field)
            {
                ctx.translate_accessor(field_def.did);
                let acc = names.accessor(adt_def.did(), subst, var_idx, field_idx.into());
                let acc = Exp::impure_qvar(acc).app(vec![Exp::pure_var(ident.clone())]);
                field_inv.subst(&[(field_name.clone(), acc)].into());

                pats.push(Pattern::VarP(field_name));
                exp = exp.log_and(field_inv);
                trivial = false;
            } else {
                pats.push(Pattern::Wildcard);
            }
        }

        let var_name = names.constructor(var_def.def_id, subst);
        branches.push((Pattern::ConsP(var_name, pats), exp));
    }

    let exp = if branches.len() == 1 {
        branches.pop().unwrap().1
    } else {
        Exp::Match(Box::new(Exp::pure_var(ident)), branches)
    };

    (!trivial).then(|| exp)
}

fn resolve_user_inv<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    let trait_did = tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_user"))?;

    let (impl_did, subst) = traits::resolve_assoc_item_opt(
        tcx,
        param_env,
        trait_did,
        tcx.mk_substs(&[GenericArg::from(ty)]),
    )?;
    let subst = tcx.try_normalize_erasing_regions(param_env, subst).unwrap_or(subst);

    // if inv resolved to the default impl and is not specializable, ignore
    if impl_did == trait_did && !traits::still_specializable(tcx, param_env, impl_did, subst) {
        None
    } else {
        Some((impl_did, subst))
    }
}
