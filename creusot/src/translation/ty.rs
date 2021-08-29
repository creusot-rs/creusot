use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, subst::InternalSubsts, Ty, TyKind::*};
use rustc_span::Span;
use rustc_span::Symbol;
use std::collections::VecDeque;

use why3::declaration::TyDecl;
use why3::{mlcfg::Type as MlT, QName} ;

use crate::ctx::*;

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
pub fn translate_ty<'tcx>(ctx: &mut TranslationCtx<'_, 'tcx>, span: Span, ty: Ty<'tcx>) -> MlT {
    translate_ty_inner(TyTranslation::Usage, ctx, span, ty)
}

fn translate_ty_inner<'tcx>(
    trans: TyTranslation,
    ctx: &mut TranslationCtx<'_, 'tcx>,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    use rustc_middle::ty::FloatTy::*;

    match ty.kind() {
        Bool => MlT::Bool,
        Char => MlT::Char,
        Int(ity) => intty_to_ty(ity),
        Uint(uity) => uintty_to_ty(uity),
        Float(flty) => match flty {
            F32 => single_ty(),
            F64 => double_ty(),
        },
        Adt(def, s) => {
            if def.is_box() {
                return translate_ty_inner(trans, ctx, span, s[0].expect_ty());
            }

            if format!("{:?}", def).contains("creusot_contracts::Int") {
                return MlT::Integer;
            }
            let args = s.types().map(|t| translate_ty_inner(trans, ctx, span, t)).collect();

            MlT::TApp(box MlT::TConstructor(translate_ty_name(ctx, def.did)), args)
        }
        Tuple(args) => {
            let tys = args.types().map(|t| translate_ty_inner(trans, ctx, span, t)).collect();
            MlT::Tuple(tys)
        }
        Param(p) => {
            if let TyTranslation::Declaration = trans {
                MlT::TVar(translate_ty_param(p.name))
            } else {
                MlT::TConstructor(QName::from_string(&p.to_string().to_lowercase()).unwrap())
            }
        }
        Ref(_, ty, borkind) => {
            use rustc_ast::Mutability::*;
            match borkind {
                Mut => MlT::MutableBorrow(box translate_ty_inner(trans, ctx, span, ty)),
                Not => translate_ty_inner(trans, ctx, span, ty),
            }
        }
        Slice(ty) => MlT::TApp(
            box MlT::TConstructor("array".into()),
            vec![translate_ty_inner(trans, ctx, span, ty)],
        ),
        Str => MlT::TConstructor("string".into()),
        // Slice()
        Never => MlT::Tuple(vec![]),
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
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
                for ty in field.ty(ctx.tcx, substs).walk() {
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

fn translate_ty_param(p: Symbol) -> String {
    p.to_string().to_lowercase()
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

    let adt = ctx.tcx.adt_def(did);
    let gens = ctx.tcx.generics_of(did);

    // HACK(xavier): Clean up
    let ty_name = translate_ty_name(ctx, did).name.into();

    // Collect type variables of declaration
    let ty_args: Vec<_> = gens
        .params
        .iter()
        .filter_map(|param| match param.kind {
            ty::GenericParamDefKind::Type { .. } => Some(translate_ty_param(param.name)),
            _ => None,
        })
        .collect();

    let substs = InternalSubsts::identity_for_item(ctx.tcx, did);

    let mut ml_ty_def = Vec::new();

    for var_def in adt.variants.iter() {
        let field_tys: Vec<_> = var_def
            .fields
            .iter()
            .map(|f| {
                translate_ty_inner(TyTranslation::Declaration, ctx, span, f.ty(ctx.tcx, substs))
            })
            .collect();

        let var_name = translate_value_id(ctx.tcx, var_def.def_id);
        ml_ty_def.push((var_name.name(), field_tys));
    }

    let ty_decl = TyDecl { ty_name, ty_params: ty_args, ty_constructors: ml_ty_def };
    ctx.add_type(ty_decl);
}

fn intty_to_ty(ity: &rustc_middle::ty::IntTy) -> MlT {
    use rustc_middle::ty::IntTy::*;
    match ity {
        Isize => isize_ty(),
        I8 => i8_ty(),
        I16 => i16_ty(),
        I32 => i32_ty(),
        I64 => i64_ty(),
        I128 => unimplemented!("128 bit integers not yet implemented"),
    }
}

fn uintty_to_ty(ity: &rustc_middle::ty::UintTy) -> MlT {
    use rustc_middle::ty::UintTy::*;
    match ity {
        Usize => usize_ty(),
        U8 => u8_ty(),
        U16 => u16_ty(),
        U32 => u32_ty(),
        U64 => u64_ty(),
        U128 => unimplemented!("128 bit integers not yet implemented"),
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

pub fn isize_ty() -> MlT {
    MlT::TConstructor(QName::from_string("isize").unwrap())
}
