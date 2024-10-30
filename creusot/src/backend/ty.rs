use crate::{
    attributes::{get_builtin, is_logic, is_snap_ty, is_trusted},
    backend::{
        program::{floatty_to_prelude, int_to_prelude, uint_to_prelude},
        Dependencies, Why3Generator,
    },
    ctx::*,
    naming::{item_name, module_name, translate_accessor_name},
    specification::PreSignature,
    translation::{
        pearlite::{self, Term, TermKind},
        specification::PreContract,
    },
    util::erased_identity_for_item,
};
use indexmap::IndexSet;
use petgraph::{algo::tarjan_scc, graphmap::DiGraphMap};
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{
    self, AliasTy, AliasTyKind, EarlyBinder, FieldDef, GenericArg, GenericArgKind, GenericArgsRef,
    ParamEnv, Ty, TyCtxt, TyKind,
};
use rustc_span::{Span, Symbol, DUMMY_SP};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::{FloatTy, IntTy, TyKind::*, UintTy};
use std::collections::VecDeque;
use why3::{
    declaration::{
        AdtDecl, ConstructorDecl, Contract, Decl, Field, Logic, Module, Signature, TyDecl, Use,
    },
    exp::{Binder, Exp, Pattern, Trigger},
    ty::Type as MlT,
    Ident, QName,
};

/// When we translate a type declaration, generic parameters should be declared using 't notation:
///
///   struct A<T>(T) -> type 't a = 't
///
/// while when we use a generic type, the generic parameters should have been pre-declared in the
/// surrounding module.
///
/// fn x<T>(a: T) {..} -> type t; let x (a : t) = ..
///
/// This enum selects the two behaviors
/// TODO: perhaps a cleaner solution would be to carry a substitution which chooses how to replace
/// tyvars with us. Do this if we change the tyvars again.
#[derive(Copy, Clone, PartialEq, Eq)]
enum TyTranslation {
    Declaration(DefId),
    Usage,
}

// Translate a type usage
pub(crate) fn translate_ty<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    translate_ty_inner(TyTranslation::Usage, ctx, names, span, ty)
}

fn translate_ty_inner<'tcx, N: Namer<'tcx>>(
    trans: TyTranslation,
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    match ty.kind() {
        Bool => MlT::Bool,
        Char => {
            names.import_prelude_module(PreludeModule::Char);
            MlT::Char
        }
        Int(ity) => intty_to_ty(names, *ity),
        Uint(uity) => uintty_to_ty(names, *uity),
        Float(flty) => floatty_to_ty(names, *flty),
        Adt(def, s) => {
            if def.is_box() {
                return translate_ty_inner(trans, ctx, names, span, s[0].expect_ty());
            }

            if is_int(ctx.tcx, ty) {
                names.import_prelude_module(PreludeModule::Int);
                return MlT::Integer;
            }

            let cons = if let Some(builtin) =
                get_builtin(ctx.tcx, def.did()).map(|a| QName::from_string(&a.as_str()))
            {
                names.ty(def.did(), s);
                MlT::TConstructor(builtin.without_search_path())
            } else {
                ctx.translate(def.did());
                MlT::TConstructor(names.ty(def.did(), s))
            };

            let mut args: Vec<_> =
                s.types().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();

            let adt_projs: Vec<_> = ctx.projections_in_ty(def.did()).to_owned();
            let tcx = ctx.tcx;
            args.extend(adt_projs.iter().map(|t| {
                let ty = EarlyBinder::bind(t.to_ty(tcx)).instantiate(tcx, s);
                translate_ty_inner(trans, ctx, names, span, ty)
            }));
            MlT::TApp(Box::new(cons), args)
        }
        Tuple(ref args) => {
            let tys =
                (*args).iter().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();
            MlT::Tuple(tys)
        }
        Param(_) => {
            let qname = names.ty_param(ty);
            if let TyTranslation::Declaration(_) = trans {
                MlT::TVar(qname.as_ident())
            } else {
                MlT::TConstructor(qname)
            }
        }
        Alias(AliasTyKind::Projection, pty) => translate_projection_ty(trans, ctx, names, pty),
        Ref(_, ty, borkind) => {
            use rustc_ast::Mutability::*;
            names.import_prelude_module(PreludeModule::Borrow);
            match borkind {
                Mut => {
                    MlT::MutableBorrow(Box::new(translate_ty_inner(trans, ctx, names, span, *ty)))
                }
                Not => translate_ty_inner(trans, ctx, names, span, *ty),
            }
        }
        Slice(ty) => {
            names.import_prelude_module(PreludeModule::Slice);
            MlT::TApp(
                Box::new(MlT::TConstructor("slice".into())),
                vec![translate_ty_inner(trans, ctx, names, span, *ty)],
            )
        }
        Array(ty, _) => {
            names.import_prelude_module(PreludeModule::Slice);
            MlT::TApp(
                Box::new(MlT::TConstructor("array".into())),
                vec![translate_ty_inner(trans, ctx, names, span, *ty)],
            )
        }
        Str => MlT::TConstructor("string".into()),
        // Slice()
        Never => MlT::Tuple(vec![]),
        RawPtr(_, _) => {
            names.import_prelude_module(PreludeModule::Opaque);
            MlT::TConstructor(QName::from_string("opaque_ptr"))
        }
        Closure(id, subst) => {
            ctx.translate(*id);

            if is_logic(ctx.tcx, *id) {
                return MlT::Tuple(Vec::new());
            }

            let args = subst
                .as_closure()
                .parent_args()
                .iter()
                .filter_map(|t| match t.unpack() {
                    GenericArgKind::Type(t) => Some(translate_ty_inner(trans, ctx, names, span, t)),
                    _ => None,
                })
                .collect();

            let cons = MlT::TConstructor(names.ty(*id, subst));

            cons.tapp(args)
        }
        FnDef(_, _) =>
        /* FnDef types are effectively singleton types, so it is sound to translate to unit. */
        {
            MlT::Tuple(vec![])
        }
        FnPtr(_) => {
            names.import_prelude_module(PreludeModule::Opaque);
            MlT::TConstructor(QName::from_string("opaque_ptr"))
        }
        Dynamic(_, _, _) => {
            names.import_prelude_module(PreludeModule::Opaque);
            MlT::TConstructor(QName::from_string("dyn"))
        }

        Foreign(_) => {
            names.import_prelude_module(PreludeModule::Opaque);
            MlT::TConstructor(QName::from_string("foreign"))
        }
        Error(_) => MlT::UNIT,
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

fn translate_projection_ty<'tcx, N: Namer<'tcx>>(
    mode: TyTranslation,
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    pty: &AliasTy<'tcx>,
) -> MlT {
    if let TyTranslation::Declaration(id) = mode {
        let ix = ctx.projections_in_ty(id).iter().position(|t| t == pty).unwrap();
        return MlT::TVar(Ident::build(&format!("proj{ix}")));
    } else {
        let ty = Ty::new_alias(ctx.tcx, AliasTyKind::Projection, *pty);
        let proj_ty = names.normalize(ctx, ty);
        if let TyKind::Alias(AliasTyKind::Projection, aty) = proj_ty.kind() {
            return MlT::TConstructor(names.ty(aty.def_id, aty.args));
        };
        translate_ty(ctx, names, DUMMY_SP, proj_ty)
    }
}

pub(crate) fn translate_closure_ty<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> TyDecl {
    let ty_name = names.ty(did, subst).as_ident();
    let closure_subst = subst.as_closure();
    let fields: Vec<_> = closure_subst
        .upvar_tys()
        .iter()
        .map(|uv| Field {
            ty: translate_ty_inner(TyTranslation::Declaration(did), ctx, names, DUMMY_SP, uv),
            ghost: false,
        })
        .collect();

    let cons_name = names.constructor(did, subst).as_ident();
    let kind = AdtDecl {
        ty_name,
        ty_params: ty_param_names(names, did).collect(),
        constrs: vec![ConstructorDecl { name: cons_name, fields }],
    };

    TyDecl::Adt { tys: vec![kind] }
}

pub(crate) fn ty_binding_group<'tcx>(tcx: TyCtxt<'tcx>, ty_id: DefId) -> IndexSet<DefId> {
    let mut graph = DiGraphMap::<_, ()>::new();
    graph.add_node(ty_id);

    let mut to_visit = VecDeque::new();
    to_visit.push_back(ty_id);

    // Construct graph of type dependencies
    while let Some(next) = to_visit.pop_front() {
        let def = tcx.adt_def(next);
        let substs = erased_identity_for_item(tcx, def.did());

        // TODO: Look up a more efficient way of getting this info
        for variant in def.variants() {
            for field in &variant.fields {
                for ty in field.ty(tcx, substs).walk() {
                    let k = match ty.unpack() {
                        GenericArgKind::Type(ty) => ty,
                        _ => continue,
                    };
                    if let Adt(def, _) = k.kind() {
                        if !graph.contains_node(def.did()) {
                            to_visit.push_back(def.did());
                        }
                        graph.add_edge(next, def.did(), ());
                    }
                }
            }
        }
    }

    // Calculate SCCs
    let sccs = tarjan_scc(&graph);
    let group: IndexSet<DefId> = sccs.last().unwrap().into_iter().cloned().collect();
    assert!(group.contains(&ty_id));

    group
}

impl<'tcx> Why3Generator<'tcx> {
    pub(super) fn get_projections_in_ty(&mut self, def_id: DefId) -> Vec<AliasTy<'tcx>> {
        let mut v = Vec::new();
        let param_env = self.param_env(def_id);

        // FIXME: Make this a proper BFS / DFS
        let subst = erased_identity_for_item(self.tcx, def_id);
        for f in self.adt_def(def_id).all_fields() {
            let ty = f.ty(self.tcx, subst);
            let ty = self.try_normalize_erasing_regions(param_env, ty).unwrap_or(ty);
            match ty.kind() {
                TyKind::Alias(AliasTyKind::Projection, aty) => v.push(*aty),
                TyKind::Adt(adt, substs) => {
                    let tcx = self.tcx;
                    for proj in self.projections_in_ty(adt.did()) {
                        let proj = EarlyBinder::bind(proj.to_ty(tcx)).instantiate(tcx, substs);
                        if let TyKind::Alias(AliasTyKind::Projection, aty) = proj.kind() {
                            v.push(*aty)
                        }
                    }

                    // Add projections of types appearing in the substitution of a field.
                    for a in
                        substs.iter().flat_map(GenericArg::walk).filter_map(GenericArg::as_type)
                    {
                        match a.kind() {
                            TyKind::Alias(AliasTyKind::Projection, aty) => v.push(*aty),
                            _ => {}
                        };
                    }
                    // v.extend(self.projections_in_ty(adt.did()))
                }
                _ => {}
            }
        }
        v
    }
}

// Translate a Rust type declation to an ML one
// Rust tuple-like types are translated as one would expect, to product types in WhyML
// However, Rust struct types are *not* translated to WhyML records, instead we 'forget' the field names
// and also translate them to product types.
//
// Additionally, types are not translated one by one but rather as a *binding group*, so that mutually
// recursive types are properly translated.
// Results are accumulated and can be collected at once by consuming the `Ctx`
pub(crate) fn translate_tydecl(
    ctx: &mut Why3Generator<'_>,
    bg: &IndexSet<DefId>,
) -> Option<Vec<Module>> {
    let repr = ctx.representative_type(bg.first().unwrap().clone());

    if get_builtin(ctx.tcx, repr).is_some() || ctx.type_of(bg[0]).skip_binder().is_box() {
        return None;
    }

    let mut names = Dependencies::new(ctx, bg.iter().copied());

    let name = module_name(ctx.tcx, repr).to_string().into();
    let span = ctx.def_span(repr);

    // Trusted types (opaque)
    if is_trusted(ctx.tcx, repr) {
        if bg.len() > 1 {
            ctx.crash_and_error(span, "cannot mark mutually recursive types as trusted");
        }
        let ty_name = item_name(ctx.tcx, repr, Namespace::TypeNS);

        let ty_params: Vec<_> = ty_param_names(&mut names, repr).collect();
        let modl = Module {
            name,
            decls: vec![Decl::TyDecl(TyDecl::Opaque { ty_name, ty_params })],
            attrs: Vec::from_iter(ctx.span_attr(ctx.def_span(repr))),
            meta: ctx.display_impl_of(repr),
        };
        let _ = names.provide_deps(ctx);
        return Some(vec![modl]);
    }

    let ty_decl =
        TyDecl::Adt { tys: bg.iter().map(|did| build_ty_decl(ctx, &mut names, *did)).collect() };

    let mut destructors = vec![];
    for did in bg.iter() {
        let adt_def = ctx.adt_def(*did);
        for vix in adt_def.variants().indices() {
            let d = destructor(ctx, &mut names, *did, ctx.type_of(*did).skip_binder(), vix);
            destructors.push(d)
        }
    }

    let mut decls = names.provide_deps(ctx);
    decls.push(Decl::TyDecl(ty_decl));

    decls.extend(destructors);

    let attrs = Vec::from_iter(ctx.span_attr(span));
    let mut modls = vec![Module { name: name.clone(), decls, attrs, meta: None }];

    modls.extend(bg.iter().filter(|did| **did != repr).map(|did| Module {
        name: module_name(ctx.tcx, *did).to_string().into(),
        decls: vec![Decl::UseDecl(Use { name: name.clone().into(), as_: None, export: true })],
        attrs: Vec::from_iter(ctx.span_attr(ctx.def_span(did))),
        meta: ctx.display_impl_of(*did),
    }));

    Some(modls)
}

pub(crate) fn field_names_and_tys<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    ty: Ty<'tcx>,
    variant: VariantIdx,
) -> Vec<(Symbol, Ty<'tcx>)> {
    match ty.kind() {
        Adt(def, subst) => {
            let variant = &def.variants()[variant];

            let field_tys: Vec<_> = variant
                .fields
                .iter()
                .map(|fld| {
                    let fld_ty = fld.ty(ctx.tcx, subst);
                    if fld.name.as_str().as_bytes()[0].is_ascii_digit() {
                        (Symbol::intern(&format!("field_{}", fld.name)), fld_ty)
                    } else {
                        (fld.name, fld_ty)
                    }
                })
                .collect();

            field_tys
        }
        Closure(def_id, subst) => {
            let captures = ctx.closure_captures(def_id.expect_local());
            let cs = subst;
            captures
                .iter()
                .zip(cs.as_closure().upvar_tys())
                .map(|(cap, ty)| (cap.to_symbol(), ty))
                .collect()
        }
        _ => vec![],
    }
}

fn id_of_ty<'tcx>(ty: Ty<'tcx>) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    match ty.kind() {
        TyKind::Adt(adt, subst) => Some((adt.did(), subst)),
        TyKind::Closure(id, subst) => Some((*id, subst)),
        _ => None,
    }
}

fn variant_id<'tcx>(parent: Ty<'tcx>, variant_ix: VariantIdx) -> DefId {
    match parent.kind() {
        TyKind::Adt(adt, _) => adt.variants()[variant_ix].def_id,
        TyKind::Closure(id, _) => {
            assert!(variant_ix == 0u32.into());
            *id
        }
        _ => unreachable!(),
    }
}

pub(crate) fn destructor<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    _: DefId,
    base_ty: Ty<'tcx>,
    variant: VariantIdx,
) -> Decl {
    use why3::coma::{self, Arg, Defn, Expr, Param};

    let Some((ty_id, subst)) = id_of_ty(base_ty) else { unreachable!() };

    let decl = TyTranslation::Declaration(ty_id);
    let fields: Vec<_> = field_names_and_tys(ctx, base_ty, variant)
        .into_iter()
        .map(|(nm, ty)| {
            let ty = names.normalize(ctx, ty);
            (Ident::build(nm.as_str()), translate_ty_inner(decl, ctx, names, DUMMY_SP, ty))
        })
        .collect();

    let field_args: Vec<coma::Param> =
        fields.iter().cloned().map(|(nm, ty)| Param::Term(nm, ty)).collect();

    let cons_id = variant_id(base_ty, variant);
    let constr = names.constructor(cons_id, subst);
    let cons_test =
        Exp::qvar(constr).app(fields.iter().map(|(nm, _)| nm.clone()).map(Exp::var).collect());

    let ret = Expr::Symbol("ret".into())
        .app(fields.iter().map(|(nm, _)| Exp::var(nm.clone())).map(Arg::Term).collect());

    let good_branch: coma::Defn = coma::Defn {
        name: format!("good").into(),
        writes: vec![],
        params: field_args.clone(),
        body: Expr::Assert(
            Box::new(cons_test.clone().eq(Exp::var("input"))),
            Box::new(Expr::BlackBox(Box::new(ret))),
        ),
    };
    let num_variants = match base_ty.kind() {
        TyKind::Adt(def, _) => def.variants().len(),
        _ => 1,
    };

    let bad_branch = if num_variants > 1 {
        let fail =
            Expr::BlackBox(Box::new(Expr::Assert(Box::new(Exp::mk_false()), Box::new(Expr::Any))));

        let fields: Vec<_> = fields.iter().cloned().collect();
        let negative_assertion = if fields.is_empty() {
            cons_test.neq(Exp::var("input"))
        } else {
            // TODO: Replace this with a pattern match to generat more readable goals
            let ty = translate_ty_inner(
                TyTranslation::Declaration(ty_id),
                ctx,
                names,
                DUMMY_SP,
                base_ty,
            );
            Exp::Forall(
                fields,
                vec![Trigger::single(cons_test.clone().ascribe(ty))],
                Box::new(cons_test.neq(Exp::var("input"))),
            )
        };

        Some(coma::Defn {
            name: format!("bad").into(),
            writes: vec![],
            params: vec![],
            body: Expr::Assert(Box::new(negative_assertion), Box::new(fail)),
        })
    } else {
        None
    };

    let ret_cont = Param::Cont("ret".into(), Vec::new(), field_args);

    let input =
        Param::Term("input".into(), translate_ty_inner(decl, ctx, names, DUMMY_SP, base_ty));
    use why3::ty::Type;

    let params = ty_params(ctx, names, ty_id)
        .map(|ty| Param::Ty(Type::TVar(ty)))
        .chain([input, ret_cont])
        .collect();

    let branches = std::iter::once(good_branch).chain(bad_branch).collect();
    Decl::Coma(Defn {
        name: names.eliminator(cons_id, subst).as_ident(),
        writes: vec![],
        params,
        body: Expr::Defn(Box::new(Expr::Any), false, branches),
    })
}

fn build_ty_decl<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    did: DefId,
) -> AdtDecl {
    let adt = ctx.tcx.adt_def(did);
    let substs = erased_identity_for_item(ctx.tcx, did);

    // HACK(xavier): Clean up
    let ty_name = names.ty(did, substs).as_ident();

    // Collect type variables of declaration
    let ty_args: Vec<_> = ty_params(ctx, names, did).collect();

    let param_env = ctx.param_env(did);
    let kind = {
        let mut ml_ty_def = Vec::new();

        for var_def in adt.variants().iter() {
            ml_ty_def.push(ConstructorDecl {
                name: names.constructor(var_def.def_id, substs).as_ident(),
                fields: var_def
                    .fields
                    .iter()
                    .map(|f| {
                        let ty = field_ty(ctx, names, param_env, did, f, substs);
                        Field { ty, ghost: false }
                    })
                    .collect(),
            });
        }

        AdtDecl { ty_name, ty_params: ty_args, constrs: ml_ty_def }
    };

    kind
}
use rustc_data_structures::captures::Captures;

fn ty_params<'tcx, 'a>(
    ctx: &'a mut Why3Generator<'tcx>,
    names: &'a mut Dependencies<'tcx>,
    did: DefId,
) -> impl Iterator<Item = Ident> + Captures<'tcx> + 'a {
    let projections = if ctx.is_closure_like(did) {
        Box::new(std::iter::empty()) as Box<dyn Iterator<Item = _>>
    } else {
        let i = ctx
            .projections_in_ty(did)
            .iter()
            .enumerate()
            .map(|(i, _)| Ident::build(&format!("proj{i}")));
        Box::new(i) as Box<dyn Iterator<Item = _>>
    };

    ty_param_names(names, did).chain(projections)
}

fn ty_param_names<'tcx, 'a>(
    names: &'a mut Dependencies<'tcx>,
    mut def_id: DefId,
) -> Box<dyn Iterator<Item = Ident> + 'a> {
    let tcx = names.tcx();
    loop {
        if tcx.is_closure_like(def_id) {
            def_id = tcx.parent(def_id);
        } else {
            break;
        }
    }

    let gens = tcx.generics_of(def_id);
    Box::new((0..gens.count()).filter_map(move |i| {
        let param = gens.param_at(i, tcx);
        match param.kind {
            ty::GenericParamDefKind::Type { .. } => {
                Some(names.ty_param(Ty::new_param(tcx, param.index, param.name)).as_ident())
            }
            _ => None,
        }
    }))
}

fn field_ty<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut Dependencies<'tcx>,
    param_env: ParamEnv<'tcx>,
    did: DefId,
    field: &FieldDef,
    substs: GenericArgsRef<'tcx>,
) -> MlT {
    let ty = field.ty(ctx.tcx, substs);
    let ty = ctx.try_normalize_erasing_regions(param_env, ty).unwrap_or(ty);

    if !validate_field_ty(ctx, did, ty) {
        ctx.crash_and_error(ctx.def_span(field.did), "Illegal use of the Snapshot type")
    }

    translate_ty_inner(TyTranslation::Declaration(did), ctx, names, ctx.def_span(field.did), ty)
}

fn validate_field_ty<'tcx>(ctx: &mut Why3Generator<'tcx>, adt_did: DefId, ty: Ty<'tcx>) -> bool {
    let tcx = ctx.tcx;
    let bg = ctx.binding_group(adt_did);

    !ty.walk().filter_map(ty::GenericArg::as_type).any(|ty| {
        is_snap_ty(tcx, ty)
            && ty.walk().filter_map(ty::GenericArg::as_type).any(|ty| match ty.kind() {
                TyKind::Adt(adt_def, _) => bg.contains(&adt_def.did()),
                // TyKind::Param(_) => true,
                _ => false,
            })
    })
}

pub(crate) fn translate_accessor(
    ctx: &mut Why3Generator<'_>,
    adt_did: DefId,
    variant_did: DefId,
    field_id: DefId,
) -> Decl {
    let adt_def = ctx.tcx.adt_def(adt_did);
    let variant_ix = adt_def.variant_index_with_id(variant_did);
    let variant = &adt_def.variants()[variant_ix];
    let ix = variant.fields.iter().position(|f| f.did == field_id).unwrap();
    let field = &variant.fields[ix.into()];

    let substs = erased_identity_for_item(ctx.tcx, adt_did);
    let bg: Vec<_> = ctx.binding_group(adt_did).iter().copied().collect();
    let mut names = Dependencies::new(ctx, bg);

    let acc_name = translate_accessor_name(variant.name.as_str(), field.name.as_str());

    let param_env = ctx.param_env(adt_did);
    let target_ty =
        field_ty(ctx, &mut names, param_env, adt_did, &variant.fields[ix.into()], substs);

    let variant_arities: Vec<_> = adt_def
        .variants()
        .iter()
        .map(|var| (names.constructor(var.def_id, substs), var.fields.len()))
        .collect();

    let this = translate_ty_inner(
        TyTranslation::Declaration(adt_did),
        ctx,
        &mut names,
        DUMMY_SP,
        ctx.type_of(adt_did).instantiate_identity(),
    );

    let _ = names.provide_deps(ctx);

    build_accessor(
        this,
        Ident::build(&acc_name),
        variant_ix.into(),
        &variant_arities,
        (ix, target_ty, false),
        &ctx.ctx,
    )
}

pub(crate) fn build_accessor(
    this: MlT,
    acc_name: Ident,
    variant_ix: usize,
    variant_arities: &[(QName, usize)],
    target_field: (usize, MlT, bool),
    _: &TranslationCtx<'_>,
) -> Decl {
    let field_ty = target_field.1;
    let field_ix = target_field.0;

    let sig = Signature {
        name: acc_name.clone(),
        trigger: None,
        attrs: Vec::new(),
        args: vec![Binder::typed("self".into(), this.clone())],
        retty: Some(field_ty.clone()),
        contract: Contract::new(),
    };

    let branches = variant_arities
        .into_iter()
        .enumerate()
        .map(|(ix, (name, arity))| {
            let mut pat = vec![Pattern::Wildcard; *arity];
            let mut exp = Exp::var("any_l1").app_to(Exp::var("self"));

            if ix == variant_ix {
                pat[field_ix] = Pattern::VarP("a".into());
                exp = Exp::var("a");
            };
            (Pattern::ConsP(name.clone(), pat), exp)
        })
        .collect();

    let discr_exp = Exp::Match(Box::new(Exp::var("self")), branches);

    Decl::LogicDefn(Logic { sig, body: discr_exp })
}

pub(crate) fn closure_accessors<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    closure: DefId,
) -> Vec<(Symbol, PreSignature<'tcx>, Term<'tcx>)> {
    let TyKind::Closure(_, substs) = ctx.type_of(closure).instantiate_identity().kind() else {
        unreachable!()
    };

    let count = substs.as_closure().upvar_tys().len();

    (0..count)
        .map(|i| {
            let (sig, term) = build_closure_accessor(ctx, closure, i);
            (Symbol::intern(&format!("field_{i}")), sig, term)
        })
        .collect()
}

pub(crate) fn build_closure_accessor<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    closure: DefId,
    ix: usize,
) -> (PreSignature<'tcx>, Term<'tcx>) {
    let TyKind::Closure(_, substs) = ctx.type_of(closure).instantiate_identity().kind() else {
        unreachable!()
    };

    let out_ty = substs.as_closure().upvar_tys()[ix];

    let self_ = Term::var(Symbol::intern("self"), ctx.type_of(closure).instantiate_identity());

    let pre_sig = PreSignature {
        inputs: vec![(
            Symbol::intern("self"),
            DUMMY_SP,
            ctx.type_of(closure).instantiate_identity(),
        )],
        output: out_ty,
        contract: PreContract::default(),
    };

    let res = Term::var(Symbol::intern("a"), out_ty);

    let mut fields: Vec<_> =
        substs.as_closure().upvar_tys().iter().map(|_| pearlite::Pattern::Wildcard).collect();
    fields[ix] = pearlite::Pattern::Binder(Symbol::intern("a"));

    let term = Term {
        ty: out_ty,
        kind: TermKind::Let {
            pattern: pearlite::Pattern::Constructor { variant: closure, substs, fields },
            arg: Box::new(self_),
            body: Box::new(res),
        },
        span: DUMMY_SP,
    };

    (pre_sig, term)
}

pub(crate) fn intty_to_ty<'tcx, N: Namer<'tcx>>(names: &mut N, ity: IntTy) -> MlT {
    names.import_prelude_module(int_to_prelude(ity));
    match ity {
        IntTy::Isize => MlT::TConstructor(QName::from_string("isize")),
        IntTy::I8 => MlT::TConstructor(QName::from_string("int8")),
        IntTy::I16 => MlT::TConstructor(QName::from_string("int16")),
        IntTy::I32 => MlT::TConstructor(QName::from_string("int32")),
        IntTy::I64 => MlT::TConstructor(QName::from_string("int64")),
        IntTy::I128 => MlT::TConstructor(QName::from_string("int128")),
    }
}

pub(crate) fn uintty_to_ty<'tcx, N: Namer<'tcx>>(names: &mut N, uty: UintTy) -> MlT {
    names.import_prelude_module(uint_to_prelude(uty));
    match uty {
        UintTy::Usize => MlT::TConstructor(QName::from_string("usize")),
        UintTy::U8 => MlT::TConstructor(QName::from_string("uint8")),
        UintTy::U16 => MlT::TConstructor(QName::from_string("uint16")),
        UintTy::U32 => MlT::TConstructor(QName::from_string("uint32")),
        UintTy::U64 => MlT::TConstructor(QName::from_string("uint64")),
        UintTy::U128 => MlT::TConstructor(QName::from_string("uint128")),
    }
}

pub(crate) fn floatty_to_ty<'tcx, N: Namer<'tcx>>(names: &mut N, fty: FloatTy) -> MlT {
    names.import_prelude_module(floatty_to_prelude(fty));
    match fty {
        FloatTy::F32 => MlT::TConstructor(QName::from_string("Float32.t")),
        FloatTy::F64 => MlT::TConstructor(QName::from_string("Float64.t")),
        FloatTy::F128 | FloatTy::F16 => todo!("Unsupported: {fty:?}"),
    }
}

pub fn is_int(tcx: TyCtxt, ty: Ty) -> bool {
    if let TyKind::Adt(def, _) = ty.kind() {
        tcx.is_diagnostic_item(Symbol::intern("creusot_int"), def.did())
    } else {
        false
    }
}

pub fn int_ty<'tcx, N: Namer<'tcx>>(ctx: &mut Why3Generator<'tcx>, names: &mut N) -> MlT {
    let int_id = ctx.get_diagnostic_item(Symbol::intern("creusot_int")).unwrap();
    let ty = ctx.type_of(int_id).skip_binder();
    translate_ty(ctx, names, DUMMY_SP, ty)
}
