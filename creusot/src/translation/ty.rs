use indexmap::IndexSet;
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{
    self,
    subst::{InternalSubsts, SubstsRef},
    AliasKind, AliasTy, FieldDef, GenericArgKind, Ty, TyCtxt, TyKind,
};
use rustc_span::{Span, Symbol, DUMMY_SP};
use rustc_type_ir::sty::TyKind::*;
use std::collections::VecDeque;
use why3::{
    declaration::{
        AdtDecl, ConstructorDecl, Contract, Decl, Field, LetDecl, LetKind, Module, Signature, Use,
    },
    exp::{Binder, Exp, Pattern},
    Ident,
};

use why3::{declaration::TyDecl, ty::Type as MlT, QName};

use crate::{
    ctx::*,
    util::{self, get_builtin, item_qname, module_name, PreSignature},
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
    Declaration,
    Usage,
}

// Translate a type usage
pub(crate) fn translate_ty<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    translate_ty_inner(TyTranslation::Usage, ctx, names, span, ty)
}

fn translate_ty_inner<'tcx>(
    trans: TyTranslation,
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    match ty.kind() {
        Bool => MlT::Bool,
        Char => {
            names.import_prelude_module(PreludeModule::Char);
            MlT::Char
        }
        Int(ity) => intty_to_ty(names, ity),
        Uint(uity) => uintty_to_ty(names, uity),
        Float(flty) => floatty_to_ty(names, flty),
        Adt(def, s) => {
            if def.is_box() {
                return translate_ty_inner(trans, ctx, names, span, s[0].expect_ty());
            }

            if Some(def.did()) == ctx.tcx.get_diagnostic_item(Symbol::intern("creusot_int")) {
                names.import_prelude_module(PreludeModule::Int);
                return MlT::Integer;
            }

            let cons = if let Some(builtin) =
                get_builtin(ctx.tcx, def.did()).and_then(|a| QName::from_string(&a.as_str()))
            {
                names.import_builtin_module(builtin.clone().module_qname());
                MlT::TConstructor(builtin.without_search_path())
            } else {
                ctx.translate(def.did());
                MlT::TConstructor(names.ty(def.did(), s))
            };

            let args = s.types().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();

            MlT::TApp(Box::new(cons), args)
        }
        Tuple(ref args) => {
            let tys =
                (*args).iter().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();
            MlT::Tuple(tys)
        }
        Param(p) => {
            if let TyTranslation::Declaration = trans {
                MlT::TVar(translate_ty_param(p.name))
            } else {
                MlT::TConstructor(QName::from_string(&p.to_string().to_lowercase()).unwrap())
            }
        }
        Alias(AliasKind::Projection, pty) => {
            if matches!(trans, TyTranslation::Declaration) {
                ctx.crash_and_error(span, "associated types are unsupported in type declarations")
            } else {
                translate_projection_ty(ctx, names, pty)
            }
        }
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
            names.import_prelude_module(PreludeModule::Seq);
            // names.import_prelude_module(PreludeModule:);
            MlT::TApp(
                Box::new(MlT::TConstructor("seq".into())),
                vec![translate_ty_inner(trans, ctx, names, span, *ty)],
            )
        }
        Array(ty, _) => {
            names.import_prelude_module(PreludeModule::Slice);
            names.import_prelude_module(PreludeModule::Seq);

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
                .parent_substs()
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
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

pub(crate) fn translate_projection_ty<'tcx>(
    _ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    pty: &AliasTy<'tcx>,
) -> MlT {
    // ctx.translate(pty.trait_def_id(ctx.tcx));
    let name = names.ty(pty.def_id, pty.substs);
    MlT::TConstructor(name)
}

pub(crate) fn translate_closure_ty<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    did: DefId,
    subst: SubstsRef<'tcx>,
) -> TyDecl {
    let ty_name = names.ty(did, subst).name;
    let closure_subst = subst.as_closure();
    let fields: Vec<_> = closure_subst
        .upvar_tys()
        .map(|uv| Field {
            ty: translate_ty_inner(TyTranslation::Declaration, ctx, names, DUMMY_SP, uv),
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

use petgraph::{algo::tarjan_scc, graphmap::DiGraphMap};

use super::{
    pearlite::{self, Term, TermKind},
    specification::PreContract,
};

pub(crate) fn ty_binding_group<'tcx>(tcx: TyCtxt<'tcx>, ty_id: DefId) -> IndexSet<DefId> {
    let mut graph = DiGraphMap::<_, ()>::new();
    graph.add_node(ty_id);

    let mut to_visit = VecDeque::new();
    to_visit.push_back(ty_id);

    // Construct graph of type dependencies
    while let Some(next) = to_visit.pop_front() {
        let def = tcx.adt_def(next);
        let substs = InternalSubsts::identity_for_item(tcx, def.did());

        // TODO: Look up a more efficient way of getting this info
        for variant in def.variants() {
            for field in &variant.fields {
                for ty in field.ty(tcx, substs).walk() {
                    let k = match ty.unpack() {
                        rustc_middle::ty::subst::GenericArgKind::Type(ty) => ty,
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

fn translate_ty_name(ctx: &TranslationCtx<'_>, did: DefId) -> QName {
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
pub(crate) fn translate_tydecl(ctx: &mut TranslationCtx<'_>, did: DefId) {
    let span = ctx.def_span(did);
    let bg = ctx.binding_group(did).clone();

    ctx.start_group(bg.clone());

    if let Some(_) = get_builtin(ctx.tcx, did) {
        for did in bg {
            ctx.finish(did);
        }
        return;
    }

    let repr = *bg.first().unwrap();
    let mut names = CloneMap::new(ctx.tcx, repr, CloneLevel::Stub);

    let name = module_name(ctx.tcx, repr);

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
        ctx.add_type(repr, vec![modl]);
        let _ = names.to_clones(ctx);
        for did in bg {
            ctx.finish(did);
        }
        return;
    }

    // UGLY hack to ensure that we don't explicitly use/clone the members of a binding group
    for did in &bg {
        let substs = InternalSubsts::identity_for_item(ctx.tcx, *did);
        for field in ctx.adt_def(did).all_fields() {
            for ty in field.ty(ctx.tcx, substs).walk() {
                let k = match ty.unpack() {
                    rustc_middle::ty::subst::GenericArgKind::Type(ty) => ty,
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

    let mut tys = Vec::new();
    for did in bg.iter() {
        tys.push(build_ty_decl(ctx, &mut names, *did));
    }

    let (mut decls, _) = names.to_clones(ctx);
    decls.push(Decl::TyDecl(TyDecl::Adt { tys: tys.clone() }));
    let mut modls = vec![Module { name: name.clone(), decls }];
    for did in &bg {
        ctx.finish(*did);
        if *did == repr {
            continue;
        };
        modls.push(Module {
            name: module_name(ctx.tcx, *did),
            decls: vec![Decl::UseDecl(Use { name: name.clone().into(), as_: None, export: true })],
        });
    }

    ctx.add_type(did, modls);
}

fn build_ty_decl<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    did: DefId,
) -> AdtDecl {
    let adt = ctx.tcx.adt_def(did);

    // HACK(xavier): Clean up
    let ty_name = translate_ty_name(ctx, did).name;

    // Collect type variables of declaration
    let ty_args: Vec<_> = ty_param_names(ctx.tcx, did).collect();

    let kind = {
        let substs = InternalSubsts::identity_for_item(ctx.tcx, did);
        let mut ml_ty_def = Vec::new();

        for var_def in adt.variants().iter() {
            let field_tys: Vec<_> = var_def
                .fields
                .iter()
                .map(|f| {
                    let (ty, ghost) = field_ty(ctx, names, f, substs);
                    Field { ty, ghost }
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
        if tcx.is_closure(def_id) {
            def_id = tcx.parent(def_id);
        } else {
            break;
        }
    }

    let gens = tcx.generics_of(def_id);
    gens.params
        .iter()
        .filter_map(|param| match param.kind {
            ty::GenericParamDefKind::Type { .. } => Some(translate_ty_param(param.name)),
            _ => None,
        })
        .map(Ident::from)
}

fn field_ty<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    field: &FieldDef,
    substs: SubstsRef<'tcx>,
) -> (MlT, bool) {
    (
        translate_ty_inner(
            TyTranslation::Declaration,
            ctx,
            names,
            ctx.def_span(field.did),
            field.ty(ctx.tcx, substs),
        ),
        false,
    )
}

pub(crate) fn translate_accessor(
    ctx: &mut TranslationCtx<'_>,
    adt_did: DefId,
    variant_did: DefId,
    field_id: DefId,
) -> Decl {
    let adt_def = ctx.tcx.adt_def(adt_did);
    let variant_ix = adt_def.variant_index_with_id(variant_did);
    let variant = &adt_def.variants()[variant_ix];
    let ix = variant.fields.iter().position(|f| f.did == field_id).unwrap();
    let field = &variant.fields[ix];

    let substs = InternalSubsts::identity_for_item(ctx.tcx, adt_did);
    let repr = ctx.representative_type(adt_did);
    let mut names = CloneMap::new(ctx.tcx, repr, CloneLevel::Stub);

    // UGLY hack to ensure that we don't explicitly use/clone the members of a binding group
    let bg = ctx.binding_group(repr).clone();
    for did in &bg {
        let substs = InternalSubsts::identity_for_item(ctx.tcx, *did);
        for field in ctx.adt_def(did).all_fields() {
            for ty in field.ty(ctx.tcx, substs).walk() {
                let k = match ty.unpack() {
                    rustc_middle::ty::subst::GenericArgKind::Type(ty) => ty,
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

    let ty_name = names.ty(adt_did, substs);
    let acc_name = format!("{}_{}", variant.name.as_str().to_ascii_lowercase(), field.name);

    let (target_ty, ghost) = field_ty(ctx, &mut names, &variant.fields[ix], substs);

    let variant_arities: Vec<_> = adt_def
        .variants()
        .iter()
        .map(|var| (names.constructor(var.def_id, substs), var.fields.len()))
        .collect();

    let this = MlT::TApp(
        Box::new(MlT::TConstructor(ty_name.clone().into())),
        ty_param_names(ctx.tcx, adt_did).map(MlT::TVar).collect(),
    );

    let _ = names.to_clones(ctx);

    build_accessor(
        this,
        Ident::build(&acc_name),
        variant_ix.into(),
        &variant_arities,
        (ix, target_ty, ghost),
    )
}

pub(crate) fn build_accessor(
    this: MlT,
    acc_name: Ident,
    variant_ix: usize,
    variant_arities: &[(QName, usize)],
    target_field: (usize, MlT, bool),
) -> Decl {
    let field_ty = target_field.1;
    let field_ix = target_field.0;

    let sig = Signature {
        name: acc_name.clone(),
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
                exp = Exp::pure_var("a".into());
            };
            (Pattern::ConsP(name.clone(), pat), exp)
        })
        .collect();

    let discr_exp = Exp::Match(Box::new(Exp::pure_var("self".into())), branches);

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
    let TyKind::Closure(_, substs) = ctx.type_of(closure).subst_identity().kind() else { unreachable!() };

    let count = substs.as_closure().upvar_tys().count();

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
    let TyKind::Closure(_, substs) = ctx.type_of(closure).subst_identity().kind() else { unreachable!() };

    let out_ty = substs.as_closure().upvar_tys().nth(ix).unwrap();

    let self_ = Term::var(Symbol::intern("self"), ctx.type_of(closure).subst_identity());

    let pre_sig = PreSignature {
        inputs: vec![(Symbol::intern("self"), DUMMY_SP, ctx.type_of(closure).subst_identity())],
        output: out_ty,
        contract: PreContract::default(),
    };

    let res = Term::var(Symbol::intern("a"), out_ty);

    let mut fields: Vec<_> =
        substs.as_closure().upvar_tys().map(|_| pearlite::Pattern::Wildcard).collect();
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

pub(crate) fn intty_to_ty(names: &mut CloneMap<'_>, ity: &rustc_middle::ty::IntTy) -> MlT {
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

pub(crate) fn uintty_to_ty(names: &mut CloneMap<'_>, ity: &rustc_middle::ty::UintTy) -> MlT {
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

fn floatty_to_ty(names: &mut CloneMap<'_>, fty: &rustc_middle::ty::FloatTy) -> MlT {
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
