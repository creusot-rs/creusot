use rustc_hir::def_id::DefId;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::{self, subst::InternalSubsts, ProjectionTy, Ty, TyCtxt, TyKind::*};
use rustc_middle::ty::{FieldDef, VariantDef};
use rustc_span::Span;
use rustc_span::Symbol;
use std::collections::VecDeque;
use why3::declaration::TyDeclKind;
use why3::declaration::{Axiom, Contract, Decl, Signature, ValKind};
use why3::mlcfg::{BinOp, Exp};
use why3::Ident;

use why3::declaration::TyDecl;
use why3::{mlcfg::Type as MlT, QName};

use crate::ctx::*;
use crate::util::get_builtin;

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

            if Some(def.did) == ctx.tcx.get_diagnostic_item(Symbol::intern("creusot_int")) {
                names.import_prelude_module(PreludeModule::Int);
                return MlT::Integer;
            }

            let cons = if let Some(builtin) = get_builtin(ctx.tcx, def.did) {
                names.import_builtin_module(builtin.clone().module_qname());
                MlT::TConstructor(builtin.without_search_path())
            } else {
                names.import_prelude_module(PreludeModule::Type);
                MlT::TConstructor(translate_ty_name(ctx, def.did))
            };

            let args = s.types().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();

            MlT::TApp(box cons, args)
        }
        Tuple(args) => {
            let tys =
                args.types().map(|t| translate_ty_inner(trans, ctx, names, span, t)).collect();
            MlT::Tuple(tys)
        }
        Param(p) => {
            if let TyTranslation::Declaration = trans {
                MlT::TVar(translate_ty_param(p.name))
            } else {
                MlT::TConstructor(QName::from_string(&p.to_string().to_lowercase()).unwrap())
            }
        }
        Projection(pty) => translate_projection_ty(ctx, names, pty),
        Ref(_, ty, borkind) => {
            use rustc_ast::Mutability::*;
            names.import_prelude_module(PreludeModule::Prelude);
            match borkind {
                Mut => MlT::MutableBorrow(box translate_ty_inner(trans, ctx, names, span, ty)),
                Not => translate_ty_inner(trans, ctx, names, span, ty),
            }
        }
        Slice(ty) => {
            names.import_prelude_module(PreludeModule::Prelude);
            MlT::TApp(
                box MlT::TConstructor("array".into()),
                vec![translate_ty_inner(trans, ctx, names, span, ty)],
            )
        }
        Str => MlT::TConstructor("string".into()),
        // Slice()
        Never => MlT::Tuple(vec![]),
        RawPtr(_) => {
            names.import_prelude_module(PreludeModule::Prelude);
            MlT::TConstructor(QName::from_string("opaque_ptr").unwrap())
        }
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

pub fn translate_projection_ty(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    pty: &ProjectionTy<'tcx>,
) -> MlT {
    ctx.translate_trait(pty.trait_def_id(ctx.tcx));
    let name = names.insert(pty.item_def_id, pty.substs).qname(ctx.tcx, pty.item_def_id);
    MlT::TConstructor(name)
}

use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;

pub fn check_not_mutally_recursive<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    ty_id: DefId,
    span: Span,
) {
    let mut graph = DiGraphMap::<_, ()>::new();
    graph.add_node(ty_id);

    let mut to_visit = VecDeque::new();
    to_visit.push_back(ty_id);

    // Construct graph of type dependencies
    while let Some(next) = to_visit.pop_front() {
        let def = ctx.tcx.adt_def(next);
        let substs = InternalSubsts::identity_for_item(ctx.tcx, def.did);

        // TODO: Look up a more efficient way of getting this info
        for variant in &def.variants {
            for field in &variant.fields {
                for ty in field.ty(ctx.tcx, substs).walk(ctx.tcx) {
                    let k = match ty.unpack() {
                        rustc_middle::ty::subst::GenericArgKind::Type(ty) => ty,
                        _ => continue,
                    };
                    if let Adt(def, _) = k.kind() {
                        if !graph.contains_node(def.did) {
                            to_visit.push_back(def.did);
                        }
                        graph.add_edge(next, def.did, ());
                    }
                }
            }
        }
    }

    // Calculate SCCs
    let sccs = tarjan_scc(&graph);
    let group = sccs.last().unwrap();
    assert!(group.contains(&ty_id));

    if group.len() != 1 {
        ctx.crash_and_error(span, "Mutually recursive types are not currently allowed");
    }
}

pub fn translate_ty_name(ctx: &mut TranslationCtx<'_, '_>, did: DefId) -> QName {
    // Check if we've already translated this type before.
    if !ctx.translated_items.contains(&did) {
        translate_tydecl(ctx, rustc_span::DUMMY_SP, did);
    };
    translate_type_id(ctx.tcx, did)
}

fn translate_ty_param(p: Symbol) -> Ident {
    Ident::build(&p.to_string().to_lowercase())
}

pub fn ty_name(tcx: TyCtxt, def_id: DefId) -> String {
    tcx.item_name(def_id).to_string().to_lowercase()
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
    } else {
        ctx.translated_items.insert(did);
    }

    // TODO: allow mutually recursive types
    check_not_mutally_recursive(ctx, did, span);

    let mut names = CloneMap::new(ctx.tcx, did, false);

    let adt = ctx.tcx.adt_def(did);

    // HACK(xavier): Clean up
    let ty_name = translate_ty_name(ctx, did).name;

    // Collect type variables of declaration
    let ty_args: Vec<_> = ty_param_names(ctx.tcx, did).collect();

    let substs = InternalSubsts::identity_for_item(ctx.tcx, did);

    let mut ml_ty_def = Vec::new();

    for var_def in adt.variants.iter() {
        let field_tys: Vec<_> = var_def
            .fields
            .iter()
            .map(|f| field_ty(ctx, &mut names, f, substs, rustc_span::DUMMY_SP))
            .collect();
        let var_name = translate_value_id(ctx.tcx, var_def.def_id);

        ml_ty_def.push((var_name.name(), field_tys));
    }

    let ty_decl = TyDecl { ty_name, ty_params: ty_args, kind: TyDeclKind::Adt(ml_ty_def) };
    ctx.add_type(did, ty_decl);
}

fn ty_param_names(tcx: TyCtxt<'tcx>, def_id: DefId) -> impl Iterator<Item = Ident> + 'tcx {
    let gens = tcx.generics_of(def_id);
    gens.params
        .iter()
        .filter_map(|param| match param.kind {
            ty::GenericParamDefKind::Type { .. } => Some(translate_ty_param(param.name)),
            _ => None,
        })
        .map(Ident::from)
}

fn field_ty(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    field: &FieldDef,
    substs: SubstsRef<'tcx>,
    span: Span,
) -> MlT {
    translate_ty_inner(TyTranslation::Declaration, ctx, names, span, field.ty(ctx.tcx, substs))
}

pub fn translate_accessor(
    ctx: &mut TranslationCtx<'_, '_>,
    adt_did: DefId,
    variant_did: DefId,
    field_id: DefId,
) -> Vec<Decl> {
    let adt_def = ctx.tcx.adt_def(adt_did);
    let variant = adt_def.variant_with_id(variant_did);
    let ix = variant.fields.iter().position(|f| f.did == field_id).unwrap();
    let field = &variant.fields[ix];

    let ty_name = translate_ty_name(ctx, adt_did).name();
    let acc_name = format!("{}_{}_{}", &*ty_name, variant.ident.name, field.ident.name);

    let substs = InternalSubsts::identity_for_item(ctx.tcx, adt_did);
    let mut names = CloneMap::new(ctx.tcx, adt_did, false);
    let field_tys: Vec<_> = variant
        .fields
        .iter()
        .map(|f| field_ty(ctx, &mut names, f, substs, rustc_span::DUMMY_SP))
        .collect();
    let field_ty = field_tys[ix].clone();
    let var_name = translate_value_id(ctx.tcx, variant.def_id);

    let this = MlT::TApp(
        box MlT::TConstructor(ty_name.clone().into()),
        ty_param_names(ctx.tcx, adt_did).map(MlT::TVar).collect(),
    );

    let mut sig = Signature {
        name: Ident::build(&acc_name),
        args: vec![("self".into(), this.clone())],
        retty: Some(field_ty),
        contract: Contract::new(),
    };

    let mut decls = Vec::new();

    // The function symbol
    decls.push(Decl::ValDecl(ValKind::Function { sig: sig.clone() }));

    // Ensure the program and function symbols line up
    sig.contract.ensures.push(Exp::BinaryOp(
        BinOp::Eq,
        box Exp::pure_var("result".into()),
        box Exp::pure_var(Ident::build(&acc_name)).app_to(Exp::pure_var("self".into())),
    ));
    decls.push(Decl::ValDecl(ValKind::Val { sig: sig.clone() }));

    let bound_vars: Vec<(Ident, _)> =
        ('a'..).zip(field_tys.iter()).map(|(c, t)| (c.to_string().into(), t.clone())).collect();

    // Build the generic contructor application
    let cons_app = Exp::Call(
        box Exp::pure_var(var_name.name().clone()),
        bound_vars.iter().map(|(n, _)| Exp::pure_var(n.clone())).collect(),
    );

    // The projection equality
    let projection = Exp::BinaryOp(
        BinOp::Eq,
        box Exp::Call(
            box Exp::pure_var(Ident::build(&acc_name)),
            vec![Exp::Ascribe(box cons_app, this)],
        ),
        box Exp::pure_var(bound_vars[ix].0.clone()),
    );

    // The record projection axiom
    let axiom_name = format!("{}_acc", acc_name);
    decls.push(Decl::Axiom(Axiom {
        name: Ident::build(&axiom_name),
        axiom: Exp::Forall(bound_vars, box projection),
    }));

    decls
}

pub fn variant_accessor_name(tcx: TyCtxt, def: DefId, variant: &VariantDef, field: usize) -> Ident {
    let ty_name = translate_type_id(tcx, def).name();

    format!("{}_{}_{}", &*ty_name, variant.ident.name, variant.fields[field].ident.name).into()
}

fn intty_to_ty(
    ctx: &TranslationCtx<'_, '_>,
    names: &mut CloneMap<'_>,
    ity: &rustc_middle::ty::IntTy,
) -> MlT {
    use rustc_middle::ty::IntTy::*;
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
        I8 => unimplemented!(),
        I16 => unimplemented!(),
        I32 => {
            names.import_prelude_module(PreludeModule::Int32);
            i32_ty()
        }
        I64 => {
            names.import_prelude_module(PreludeModule::Int64);
            i64_ty()
        }
        I128 => unimplemented!("128 bit integers not yet implemented"),
    }
}

fn uintty_to_ty(
    ctx: &TranslationCtx<'_, '_>,
    names: &mut CloneMap<'tcx>,
    ity: &rustc_middle::ty::UintTy,
) -> MlT {
    use rustc_middle::ty::UintTy::*;
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
        U8 => unimplemented!(),
        U16 => unimplemented!(),
        U32 => {
            names.import_prelude_module(PreludeModule::UInt32);
            u32_ty()
        }
        U64 => {
            names.import_prelude_module(PreludeModule::UInt64);
            u64_ty()
        }
        U128 => unimplemented!("128 bit integers not yet implemented"),
    }
}

fn floatty_to_ty(_: &mut CloneMap<'_>, fty: &rustc_middle::ty::FloatTy) -> MlT {
    use rustc_middle::ty::FloatTy::*;

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

pub fn u32_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint32").unwrap())
}

pub fn u64_ty() -> MlT {
    MlT::TConstructor(QName::from_string("uint64").unwrap())
}

pub fn usize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("usize").unwrap())
}

pub fn i32_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int32").unwrap())
}

pub fn i64_ty() -> MlT {
    MlT::TConstructor(QName::from_string("int64").unwrap())
}

pub fn isize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("isize").unwrap())
}
