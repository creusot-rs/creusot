use creusot_rustc::hir::def_id::DefId;
use creusot_rustc::middle::ty::subst::SubstsRef;
use creusot_rustc::middle::ty::{self, subst::InternalSubsts, ProjectionTy, Ty, TyCtxt};
use creusot_rustc::middle::ty::{ClosureSubsts, FieldDef, VariantDef};
use creusot_rustc::span::Symbol;
use creusot_rustc::span::{Span, DUMMY_SP};
use creusot_rustc::type_ir::sty::TyKind::*;
use std::collections::VecDeque;
use why3::declaration::{AdtDecl, ConstructorDecl, LetFun};
use why3::declaration::{Contract, Decl, Signature};
use why3::exp::{Exp, Pattern};
use why3::Ident;

use why3::declaration::TyDecl;
use why3::{ty::Type as MlT, QName};

use crate::util::{get_builtin, item_name, item_qname};
use crate::{ctx::*, util};

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
pub fn translate_ty<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    translate_ty_inner(TyTranslation::Usage, ctx, names, span, ty)
}

fn translate_ty_inner<'tcx>(
    trans: TyTranslation,
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    match ty.kind() {
        Bool => MlT::Bool,
        Char => MlT::Char,
        Int(ity) => intty_to_ty(ctx, names, ity),
        Uint(uity) => uintty_to_ty(ctx, names, uity),
        Float(flty) => floatty_to_ty(names, flty),
        Adt(def, s) => {
            if def.is_box() {
                return translate_ty_inner(trans, ctx, names, span, s[0].expect_ty());
            }

            if ctx.is_diagnostic_item(Symbol::intern("creusot_ghost"), def.did()) {
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
                names.import_prelude_module(PreludeModule::Type);
                MlT::TConstructor(translate_ty_name(ctx, def.did()))
            };

            let args = s.types().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();

            MlT::TApp(box cons, args)
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
        Projection(pty) => {
            if matches!(trans, TyTranslation::Declaration) {
                ctx.crash_and_error(span, "associated types are unsupported in type declarations")
            } else {
                translate_projection_ty(ctx, names, pty)
            }
        }
        Ref(_, ty, borkind) => {
            use creusot_rustc::ast::Mutability::*;
            names.import_prelude_module(PreludeModule::Prelude);
            match borkind {
                Mut => MlT::MutableBorrow(box translate_ty_inner(trans, ctx, names, span, *ty)),
                Not => translate_ty_inner(trans, ctx, names, span, *ty),
            }
        }
        Slice(ty) => {
            names.import_prelude_module(PreludeModule::Prelude);
            names.import_prelude_module(PreludeModule::Seq);
            // names.import_prelude_module(PreludeModule:);
            MlT::TApp(
                box MlT::TConstructor("seq".into()),
                vec![translate_ty_inner(trans, ctx, names, span, *ty)],
            )
        }
        Array(ty, _) => {
            names.import_prelude_module(PreludeModule::Prelude);
            names.import_prelude_module(PreludeModule::Seq);

            MlT::TApp(
                box MlT::TConstructor("rust_array".into()),
                vec![translate_ty_inner(trans, ctx, names, span, *ty)],
            )
        }
        Str => MlT::TConstructor("string".into()),
        // Slice()
        Never => MlT::Tuple(vec![]),
        RawPtr(_) => {
            names.import_prelude_module(PreludeModule::Prelude);
            MlT::TConstructor(QName::from_string("opaque_ptr").unwrap())
        }
        Closure(id, subst) => {
            ctx.translate(*id);

            let name = item_name(ctx.tcx, *id).to_string().to_lowercase();
            let cons = MlT::TConstructor(names.insert(*id, subst).qname_ident(name.into()));

            cons
        }
        FnDef(_, _) =>
        /* FnDef types are effectively singleton types, so it is sound to translate to unit. */
        {
            MlT::Tuple(vec![])
        }
        // Foreign(_) => todo!(),
        // // FnPtr(_) => todo!(),
        // FnPtr(_) => MlT::Tuple(vec![]),
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

pub fn translate_projection_ty<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    pty: &ProjectionTy<'tcx>,
) -> MlT {
    // ctx.translate(pty.trait_def_id(ctx.tcx));
    let name = names.insert(pty.item_def_id, pty.substs).qname(ctx.tcx, pty.item_def_id);
    MlT::TConstructor(name)
}

use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;

pub fn ty_binding_group<'tcx>(tcx: TyCtxt<'tcx>, ty_id: DefId) -> Vec<DefId> {
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
                        creusot_rustc::middle::ty::subst::GenericArgKind::Type(ty) => ty,
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
    let group = sccs.last().unwrap();
    assert!(group.contains(&ty_id));

    group.clone()
}

fn translate_ty_name(ctx: &mut TranslationCtx<'_, '_>, did: DefId) -> QName {
    // Check if we've already translated this type before.
    if !ctx.translated_items.contains(&did) {
        translate_tydecl(ctx, ctx.def_span(did), did);
    };

    let name = item_name(ctx.tcx, did).to_string().to_lowercase();

    QName { module: vec![module_name(ctx.tcx, did)], name: name.into() }
}

fn translate_ty_param(p: Symbol) -> Ident {
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
pub fn translate_tydecl(ctx: &mut TranslationCtx<'_, '_>, span: Span, did: DefId) {
    // mark this type as translated
    if ctx.translated_items.contains(&did) {
        return;
    }

    let mut names = CloneMap::new(ctx.tcx, did, false);

    let bg = ty_binding_group(ctx.tcx, did);

    for did in &bg {
        if !ctx.translated_items.insert(*did) {
            ctx.crash_and_error(
                span,
                &format!("already translated member of mutually recursive binding group {:?}", did),
            );
        }
    }

    // Trusted types (opaque)
    if util::is_trusted(ctx.tcx, bg[0]) {
        if bg.len() > 1 {
            ctx.crash_and_error(span, "cannot mark mutually recursive types as trusted");
        }
        let ty_name = translate_ty_name(ctx, did).name;

        let ty_params: Vec<_> = ty_param_names(ctx.tcx, did).collect();
        ctx.add_type(&bg, TyDecl::Opaque { ty_name, ty_params });
        let _ = names.to_clones(ctx);
        return;
    }

    let mut decls = Vec::new();
    for did in &bg {
        decls.push(build_ty_decl(ctx, &mut names, *did));
    }

    // Drain the clones
    let _ = names.to_clones(ctx);
    ctx.add_type(&bg, TyDecl::Adt { tys: decls });
}

fn build_ty_decl<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
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
            let field_tys: Vec<_> =
                var_def.fields.iter().map(|f| field_ty(ctx, names, f, substs)).collect();
            let var_name = item_name(ctx.tcx, var_def.def_id);

            ml_ty_def.push(ConstructorDecl { name: var_name, fields: field_tys });
        }

        AdtDecl { ty_name, ty_params: ty_args, constrs: ml_ty_def }
    };

    kind
}

pub fn translate_closure_ty<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    did: DefId,
    subst: SubstsRef<'tcx>,
) -> TyDecl {
    let ty_name = translate_ty_name(ctx, did).name;
    let closure_subst = subst.as_closure();
    let fields: Vec<_> = closure_subst
        .upvar_tys()
        .map(|uv| translate_ty_inner(TyTranslation::Usage, ctx, names, DUMMY_SP, uv))
        .collect();

    let mut cons_name = item_name(ctx.tcx, did);
    cons_name.capitalize();
    let kind = AdtDecl {
        ty_name,
        ty_params: vec![],
        constrs: vec![ConstructorDecl { name: cons_name, fields }],
    };

    TyDecl::Adt { tys: vec![kind] }
}

fn ty_param_names(tcx: TyCtxt<'_>, def_id: DefId) -> impl Iterator<Item = Ident> + '_ {
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
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    field: &FieldDef,
    substs: SubstsRef<'tcx>,
) -> MlT {
    translate_ty_inner(
        TyTranslation::Declaration,
        ctx,
        names,
        ctx.def_span(field.did),
        field.ty(ctx.tcx, substs),
    )
}

pub fn translate_accessor(
    ctx: &mut TranslationCtx<'_, '_>,
    adt_did: DefId,
    variant_did: DefId,
    field_id: DefId,
) -> Decl {
    let adt_def = ctx.tcx.adt_def(adt_did);
    let variant_ix = adt_def.variant_index_with_id(variant_did);
    let variant = &adt_def.variants()[variant_ix];
    let ix = variant.fields.iter().position(|f| f.did == field_id).unwrap();
    let field = &variant.fields[ix];

    let ty_name = translate_ty_name(ctx, adt_did);
    let acc_name = format!("{}_{}_{}", &*ty_name.name(), variant.name, field.name);

    let substs = InternalSubsts::identity_for_item(ctx.tcx, adt_did);
    let mut names = CloneMap::new(ctx.tcx, adt_did, false);
    let target_ty = field_ty(ctx, &mut names, &variant.fields[ix], substs);

    let variant_arities: Vec<_> = adt_def
        .variants()
        .iter()
        .map(|var| (item_qname(ctx.tcx, var.def_id), var.fields.len()))
        .collect();

    let this = MlT::TApp(
        box MlT::TConstructor(ty_name.clone().into()),
        ty_param_names(ctx.tcx, adt_did).map(MlT::TVar).collect(),
    );

    let _ = names.to_clones(ctx);

    build_accessor(
        this,
        Ident::build(&acc_name),
        variant_ix.into(),
        &variant_arities,
        (ix, target_ty),
    )
}

pub fn build_accessor(
    this: MlT,
    acc_name: Ident,
    variant_ix: usize,
    variant_arities: &[(QName, usize)],
    target_field: (usize, MlT),
) -> Decl {
    let field_ty = target_field.1;
    let field_ix = target_field.0;

    let sig = Signature {
        name: acc_name.clone(),
        attrs: Vec::new(),
        args: vec![("self".into(), this.clone())],
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

    let discr_exp = Exp::Match(box Exp::pure_var("self".into()), branches);

    Decl::LetFun(LetFun { sig, rec: false, ghost: false, body: discr_exp })
}

pub fn closure_accessors<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    ty_id: DefId,
    subst: ClosureSubsts<'tcx>,
) -> Vec<Decl> {
    let count = subst.upvar_tys().count();

    let mut fields: Vec<_> =
        subst.upvar_tys().map(|ty| translate_ty(ctx, names, DUMMY_SP, ty)).collect();

    let mut cons_name = item_qname(ctx.tcx, ty_id);
    cons_name.name.capitalize();
    cons_name.module = vec![]; // ugly hack to fix printer

    let ty_name = translate_ty_name(ctx, ty_id).name;
    let this = MlT::TConstructor(ty_name.into());

    let mut accessors = Vec::new();

    let variant_arity = vec![(cons_name, count)];

    for tgt in fields.drain(..).enumerate() {
        let nm = closure_accessor_name(ctx.tcx, ty_id, tgt.0);
        accessors.push(build_accessor(this.clone(), nm, tgt.0, &variant_arity, tgt));
    }
    accessors
}

pub fn closure_accessor_name(tcx: TyCtxt, def: DefId, ix: usize) -> Ident {
    let ty_name = item_name(tcx, def).to_string().to_lowercase();

    format!("{}_{}", &*ty_name, ix).into()
}

pub fn variant_accessor_name(tcx: TyCtxt, def: DefId, variant: &VariantDef, field: usize) -> Ident {
    let ty_name = item_name(tcx, def).to_string().to_lowercase();

    format!("{}_{}_{}", &*ty_name, variant.name, variant.fields[field].name).into()
}

fn intty_to_ty(
    ctx: &TranslationCtx<'_, '_>,
    names: &mut CloneMap<'_>,
    ity: &creusot_rustc::middle::ty::IntTy,
) -> MlT {
    use creusot_rustc::middle::ty::IntTy::*;
    names.import_prelude_module(PreludeModule::Int);

    if !ctx.opts.bounds_check {
        return MlT::Integer;
    }

    match ity {
        Isize => {
            names.import_prelude_module(PreludeModule::Prelude);
            names.import_prelude_module(PreludeModule::Int64);
            isize_ty()
        }
        I8 => {
            names.import_prelude_module(PreludeModule::Prelude);
            names.import_prelude_module(PreludeModule::Int8);
            i8_ty()
        }
        I16 => {
            names.import_prelude_module(PreludeModule::Prelude);
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

fn uintty_to_ty(
    ctx: &TranslationCtx<'_, '_>,
    names: &mut CloneMap<'_>,
    ity: &creusot_rustc::middle::ty::UintTy,
) -> MlT {
    use creusot_rustc::middle::ty::UintTy::*;
    names.import_prelude_module(PreludeModule::Int);

    if !ctx.opts.bounds_check {
        return MlT::Integer;
    }

    match ity {
        Usize => {
            names.import_prelude_module(PreludeModule::Prelude);
            names.import_prelude_module(PreludeModule::UInt64);
            usize_ty()
        }
        U8 => {
            names.import_prelude_module(PreludeModule::Prelude);
            names.import_prelude_module(PreludeModule::UInt8);
            u8_ty()
        }
        U16 => {
            names.import_prelude_module(PreludeModule::Prelude);
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

fn floatty_to_ty(_: &mut CloneMap<'_>, fty: &creusot_rustc::middle::ty::FloatTy) -> MlT {
    use creusot_rustc::middle::ty::FloatTy::*;

    match fty {
        F32 => single_ty(),
        F64 => double_ty(),
    }
}

pub fn double_ty() -> MlT {
    MlT::TConstructor(QName::from_string("double").unwrap())
}

pub fn single_ty() -> MlT {
    MlT::TConstructor(QName::from_string("single").unwrap())
}

pub fn u8_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint8").unwrap())
}

pub fn u16_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint16").unwrap())
}

pub fn u32_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint32").unwrap())
}

pub fn u64_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint64").unwrap())
}

pub fn u128_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint128").unwrap())
}

pub fn usize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("usize").unwrap())
}

pub fn i8_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int8").unwrap())
}

pub fn i16_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int16").unwrap())
}

pub fn i32_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int32").unwrap())
}

pub fn i64_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int64").unwrap())
}

pub fn i128_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int128").unwrap())
}

pub fn isize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("isize").unwrap())
}
