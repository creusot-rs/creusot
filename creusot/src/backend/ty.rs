use super::{CloneMap, Why3Generator};
use crate::{
    ctx::*,
    translation::{
        pearlite::{self, Term, TermKind},
        specification::PreContract,
    },
    util::{self, get_builtin, item_qname, module_name, PreSignature},
};
use indexmap::IndexSet;
use petgraph::{algo::tarjan_scc, graphmap::DiGraphMap};
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{
    self, AliasKind, AliasTy, EarlyBinder, FieldDef, GenericArg, GenericArgKind, GenericArgs,
    GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind,
};
use rustc_span::{Span, Symbol, DUMMY_SP};
use rustc_type_ir::TyKind::*;
use std::collections::VecDeque;
use why3::{
    declaration::{
        AdtDecl, ConstructorDecl, Contract, Decl, Field, LetDecl, LetKind, Module, Signature,
        TyDecl, Use,
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
        Int(ity) => {
            // names.real_ty(ty);
            intty_to_ty(names, ity)
        }
        Uint(uity) => {
            // names.real_ty(ty);
            uintty_to_ty(names, uity)
        }
        Float(flty) => floatty_to_ty(names, flty),
        Adt(def, s) => {
            if def.is_box() {
                return translate_ty_inner(trans, ctx, names, span, s[0].expect_ty());
            }

            if is_int(ctx.tcx, ty) {
                names.import_prelude_module(PreludeModule::Int);
                return MlT::Integer;
            }

            let cons = if let Some(builtin) =
                get_builtin(ctx.tcx, def.did()).and_then(|a| QName::from_string(&a.as_str()))
            {
                names.ty(def.did(), s);
                // names.import_builtin_module(builtin.clone().module_qname());
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
        Param(p) => {
            if let TyTranslation::Declaration(_) = trans {
                MlT::TVar(translate_ty_param(p.name))
            } else {
                MlT::TConstructor(QName::from_string(&p.to_string().to_lowercase()).unwrap())
            }
        }
        Alias(AliasKind::Projection, pty) => translate_projection_ty(trans, ctx, names, pty),
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
        RawPtr(_) => {
            names.import_prelude_module(PreludeModule::Opaque);
            MlT::TConstructor(QName::from_string("opaque_ptr").unwrap())
        }
        Closure(id, subst) => {
            ctx.translate(*id);

            if util::is_logic(ctx.tcx, *id) {
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
            MlT::TConstructor(QName::from_string("opaque_ptr").unwrap())
        }
        Dynamic(_, _, _) => {
            names.import_prelude_module(PreludeModule::Opaque);
            MlT::TConstructor(QName::from_string("dyn").unwrap())
        }

        Foreign(_) => {
            names.import_prelude_module(PreludeModule::Opaque);
            MlT::TConstructor(QName::from_string("foreign").unwrap())
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
        let ty = Ty::new_alias(ctx.tcx, AliasKind::Projection, *pty);
        let proj_ty = names.normalize(ctx, ty);
        if let TyKind::Alias(AliasKind::Projection, aty) = proj_ty.kind() {
            return MlT::TConstructor(names.ty(aty.def_id, aty.args));
        };
        translate_ty(ctx, names, DUMMY_SP, proj_ty)
    }
}

pub(crate) fn translate_closure_ty<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> TyDecl {
    let ty_name = names.ty(did, subst).name;
    let closure_subst = subst.as_closure();
    let fields: Vec<_> = closure_subst
        .upvar_tys()
        .iter()
        .map(|uv| Field {
            ty: translate_ty_inner(TyTranslation::Declaration(did), ctx, names, DUMMY_SP, uv),
            ghost: false,
        })
        .collect();

    let cons_name = names.constructor(did, subst).name;
    let kind = AdtDecl {
        ty_name,
        ty_params: ty_param_names(ctx.tcx, did).collect(),
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
        let substs = GenericArgs::identity_for_item(tcx, def.did());

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
        let subst = GenericArgs::identity_for_item(self.tcx, def_id);
        for f in self.adt_def(def_id).all_fields() {
            let ty = f.ty(self.tcx, subst);
            let ty = self.try_normalize_erasing_regions(param_env, ty).unwrap_or(ty);
            match ty.kind() {
                TyKind::Alias(AliasKind::Projection, aty) => v.push(*aty),
                TyKind::Adt(adt, substs) => {
                    let tcx = self.tcx;
                    for proj in self.projections_in_ty(adt.did()) {
                        let proj = EarlyBinder::bind(proj.to_ty(tcx)).instantiate(tcx, substs);
                        if let TyKind::Alias(AliasKind::Projection, aty) = proj.kind() {
                            v.push(*aty)
                        }
                    }

                    // Add projections of types appearing in the substitution of a field.
                    for a in
                        substs.iter().flat_map(GenericArg::walk).filter_map(GenericArg::as_type)
                    {
                        match a.kind() {
                            TyKind::Alias(AliasKind::Projection, aty) => v.push(*aty),
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

fn translate_ty_name(ctx: &Why3Generator<'_>, did: DefId) -> QName {
    item_qname(ctx, did, Namespace::TypeNS)
}

pub(crate) fn translate_ty_param(p: Symbol) -> Ident {
    Ident::build(&p.to_string().to_lowercase())
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

    if let Some(_) = get_builtin(ctx.tcx, repr) {
        return None;
    }

    let mut names = CloneMap::new(ctx.tcx, repr.into());

    let name = module_name(ctx.tcx, repr);
    let span = ctx.def_span(repr);

    // Trusted types (opaque)
    if util::is_trusted(ctx.tcx, repr) {
        if bg.len() > 1 {
            ctx.crash_and_error(span, "cannot mark mutually recursive types as trusted");
        }
        let ty_name = translate_ty_name(ctx, repr).name;

        let ty_params: Vec<_> = ty_param_names(ctx.tcx, repr).collect();
        let modl = Module {
            name,
            decls: vec![Decl::TyDecl(TyDecl::Opaque {
                ty_name: ty_name.clone(),
                ty_params: ty_params.clone(),
            })],
        };
        let _ = names.to_clones(ctx, CloneDepth::Shallow);
        return Some(vec![modl]);
    }

    // UGLY hack to ensure that we don't explicitly use/clone the members of a binding group
    for did in bg {
        let substs = GenericArgs::identity_for_item(ctx.tcx, *did);
        for field in ctx.adt_def(did).all_fields() {
            for ty in field.ty(ctx.tcx, substs).walk() {
                let k = match ty.unpack() {
                    GenericArgKind::Type(ty) => ty,
                    _ => continue,
                };
                if let Adt(def, sub) = k.kind() {
                    if bg.contains(&def.did()) {
                        names.insert_hidden(def.did(), sub);
                    }
                }
            }
        }
    }

    let ty_decl =
        TyDecl::Adt { tys: bg.iter().map(|did| build_ty_decl(ctx, &mut names, *did)).collect() };

    let (mut decls, _) = names.to_clones(ctx, CloneDepth::Shallow);
    decls.push(Decl::TyDecl(ty_decl));

    let mut modls = vec![Module { name: name.clone(), decls }];

    modls.extend(bg.iter().filter(|did| **did != repr).map(|did| Module {
        name: module_name(ctx.tcx, *did),
        decls: vec![Decl::UseDecl(Use { name: name.clone().into(), as_: None, export: true })],
    }));

    Some(modls)
}

fn build_ty_decl<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    did: DefId,
) -> AdtDecl {
    let adt = ctx.tcx.adt_def(did);

    // HACK(xavier): Clean up
    let ty_name = translate_ty_name(ctx, did).name;

    // Collect type variables of declaration
    let ty_args: Vec<_> = ty_param_names(ctx.tcx, did)
        .chain(
            ctx.projections_in_ty(did)
                .iter()
                .enumerate()
                .map(|(i, _)| Ident::build(&format!("proj{i}"))),
        )
        .collect();

    let param_env = ctx.param_env(did);
    let kind = {
        let substs = GenericArgs::identity_for_item(ctx.tcx, did);
        let mut ml_ty_def = Vec::new();

        for var_def in adt.variants().iter() {
            let field_tys: Vec<_> = var_def
                .fields
                .iter()
                .map(|f| {
                    let ty = field_ty(ctx, names, param_env, did, f, substs);
                    Field { ty, ghost: false }
                })
                .collect();
            let var_name = names.constructor(var_def.def_id, substs);

            ml_ty_def.push(ConstructorDecl { name: var_name.name, fields: field_tys });
        }

        AdtDecl { ty_name, ty_params: ty_args, constrs: ml_ty_def }
    };

    kind
}

pub(crate) fn ty_param_names(
    tcx: TyCtxt<'_>,
    mut def_id: DefId,
) -> impl Iterator<Item = Ident> + '_ {
    loop {
        if tcx.is_closure_or_coroutine(def_id) {
            def_id = tcx.parent(def_id);
        } else {
            break;
        }
    }

    let gens = tcx.generics_of(def_id);
    (0..gens.count()).map(move |i| gens.param_at(i, tcx)).filter_map(|param| match param.kind {
        ty::GenericParamDefKind::Type { .. } => Some(translate_ty_param(param.name)),
        _ => None,
    })
}

fn field_ty<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
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
        util::is_snap_ty(tcx, ty)
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

    let substs = GenericArgs::identity_for_item(ctx.tcx, adt_did);
    let repr = ctx.representative_type(adt_did);
    let mut names = CloneMap::new(ctx.tcx, repr.into());

    // UGLY hack to ensure that we don't explicitly use/clone the members of a binding group
    let bg = ctx.binding_group(repr).clone();
    for did in &bg {
        let substs = GenericArgs::identity_for_item(ctx.tcx, *did);
        for field in ctx.adt_def(did).all_fields() {
            for ty in field.ty(ctx.tcx, substs).walk() {
                let k = match ty.unpack() {
                    GenericArgKind::Type(ty) => ty,
                    _ => continue,
                };
                if let Adt(def, sub) = k.kind() {
                    if bg.contains(&def.did()) {
                        names.insert_hidden(def.did(), sub);
                    }
                }
            }
        }
    }

    let acc_name = format!("{}_{}", variant.name.as_str().to_ascii_lowercase(), field.name);

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

    let _ = names.to_clones(ctx, CloneDepth::Shallow);

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
    ctx: &TranslationCtx<'_>,
) -> Decl {
    let field_ty = target_field.1;
    let field_ix = target_field.0;

    let trigger = if ctx.opts.simple_triggers { None } else { Some(Trigger::NONE) };

    let sig = Signature {
        name: acc_name.clone(),
        trigger,
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
            let mut exp = Exp::Any(field_ty.clone());
            if ix == variant_ix {
                pat[field_ix] = Pattern::VarP("a".into());
                exp = Exp::var("a");
            };
            (Pattern::ConsP(name.clone(), pat), exp)
        })
        .collect();

    let discr_exp = Exp::Match(Box::new(Exp::var("self")), branches);

    Decl::Let(LetDecl {
        sig,
        rec: false,
        ghost: target_field.2,
        body: discr_exp,
        kind: Some(LetKind::Function),
    })
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
            pattern: pearlite::Pattern::Constructor {
                adt: closure,
                substs,
                variant: 0u32.into(),
                fields,
            },
            arg: Box::new(self_),
            body: Box::new(res),
        },
        span: DUMMY_SP,
    };

    (pre_sig, term)
}

pub(crate) fn intty_to_ty<'tcx, N: Namer<'tcx>>(
    names: &mut N,
    ity: &rustc_middle::ty::IntTy,
) -> MlT {
    use rustc_middle::ty::IntTy::*;
    names.import_prelude_module(PreludeModule::Int);
    match ity {
        Isize => {
            names.import_prelude_module(PreludeModule::Isize);
            isize_ty()
        }
        I8 => {
            names.import_prelude_module(PreludeModule::Int8);
            i8_ty()
        }
        I16 => {
            names.import_prelude_module(PreludeModule::Int16);
            i16_ty()
        }
        I32 => {
            names.import_prelude_module(PreludeModule::Int32);
            i32_ty()
        }
        I64 => {
            names.import_prelude_module(PreludeModule::Int64);
            i64_ty()
        }
        I128 => {
            names.import_prelude_module(PreludeModule::Int128);
            i128_ty()
        }
    }
}

pub(crate) fn uintty_to_ty<'tcx, N: Namer<'tcx>>(
    names: &mut N,
    ity: &rustc_middle::ty::UintTy,
) -> MlT {
    use rustc_middle::ty::UintTy::*;
    names.import_prelude_module(PreludeModule::Int);

    match ity {
        Usize => {
            names.import_prelude_module(PreludeModule::Usize);
            usize_ty()
        }
        U8 => {
            names.import_prelude_module(PreludeModule::UInt8);
            u8_ty()
        }
        U16 => {
            names.import_prelude_module(PreludeModule::UInt16);
            u16_ty()
        }
        U32 => {
            names.import_prelude_module(PreludeModule::UInt32);
            u32_ty()
        }
        U64 => {
            names.import_prelude_module(PreludeModule::UInt64);
            u64_ty()
        }
        U128 => {
            names.import_prelude_module(PreludeModule::UInt128);
            u128_ty()
        }
    }
}

pub(crate) fn floatty_to_ty<'tcx, N: Namer<'tcx>>(
    names: &mut N,
    fty: &rustc_middle::ty::FloatTy,
) -> MlT {
    use rustc_middle::ty::FloatTy::*;

    match fty {
        F32 => {
            names.import_prelude_module(PreludeModule::Float32);
            single_ty()
        }
        F64 => {
            names.import_prelude_module(PreludeModule::Float64);
            double_ty()
        }
    }
}

pub fn is_int(tcx: TyCtxt, ty: Ty) -> bool {
    if let TyKind::Adt(def, _) = ty.kind() {
        Some(def.did()) == tcx.get_diagnostic_item(Symbol::intern("creusot_int"))
    } else {
        false
    }
}

pub(crate) fn double_ty() -> MlT {
    MlT::TConstructor(QName::from_string("Float64.t").unwrap())
}

pub(crate) fn single_ty() -> MlT {
    MlT::TConstructor(QName::from_string("Float32.t").unwrap())
}

pub(crate) fn u8_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint8").unwrap())
}

pub(crate) fn u16_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint16").unwrap())
}

pub(crate) fn u32_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint32").unwrap())
}

pub(crate) fn u64_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint64").unwrap())
}

pub(crate) fn u128_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint128").unwrap())
}

pub(crate) fn usize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("usize").unwrap())
}

pub(crate) fn i8_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int8").unwrap())
}

pub(crate) fn i16_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int16").unwrap())
}

pub(crate) fn i32_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int32").unwrap())
}

pub(crate) fn i64_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int64").unwrap())
}

pub(crate) fn i128_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int128").unwrap())
}

pub(crate) fn isize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("isize").unwrap())
}
