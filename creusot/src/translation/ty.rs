use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{subst::InternalSubsts, ProjectionTy, Ty, TyCtxt},
    resolve::Namespace,
    span::{Span, Symbol},
    type_ir::sty::TyKind::*,
};
use indexmap::IndexSet;
use std::collections::VecDeque;
use why3::Ident;

use why3::{ty::Type as MlT, QName};

use crate::{
    ctx::*,
    util::{self, get_builtin, item_name, item_qname},
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
#[allow(dead_code)]
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
            ctx.warn(span, "support for string types is partial and experimental, expect to encounter limitations.");
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
                names.insert(def.did(), s); // TODO: Overhaul `CloneInfo` so we can use that to build type names
                MlT::TConstructor(item_qname(ctx, def.did(), Namespace::TypeNS))
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
            names.import_prelude_module(PreludeModule::Borrow);
            match borkind {
                Mut => MlT::MutableBorrow(box translate_ty_inner(trans, ctx, names, span, *ty)),
                Not => translate_ty_inner(trans, ctx, names, span, *ty),
            }
        }
        Slice(ty) => {
            names.import_prelude_module(PreludeModule::Slice);
            names.import_prelude_module(PreludeModule::Seq);
            // names.import_prelude_module(PreludeModule:);
            MlT::TApp(
                box MlT::TConstructor("seq".into()),
                vec![translate_ty_inner(trans, ctx, names, span, *ty)],
            )
        }
        Array(ty, _) => {
            names.import_prelude_module(PreludeModule::Slice);
            names.import_prelude_module(PreludeModule::Seq);

            MlT::TApp(
                box MlT::TConstructor("rust_array".into()),
                vec![translate_ty_inner(trans, ctx, names, span, *ty)],
            )
        }
        Str => {
            ctx.warn(span, "support for string types is partial and experimental, expect to encounter limitations.");
            MlT::TConstructor("string".into())
        }
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

            let cons = MlT::TConstructor(names.ty(*id, subst));

            cons
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
        // Foreign(_) => todo!(),
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

pub(crate) fn translate_projection_ty<'tcx>(
    _: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    pty: &ProjectionTy<'tcx>,
) -> MlT {
    // ctx.translate(pty.trait_def_id(ctx.tcx));
    let name = names.ty(pty.item_def_id, pty.substs);
    MlT::TConstructor(name)
}

use petgraph::{algo::tarjan_scc, graphmap::DiGraphMap};

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
    let group: IndexSet<DefId> = sccs.last().unwrap().into_iter().cloned().collect();
    assert!(group.contains(&ty_id));

    group
}

pub(crate) fn translate_ty_param(p: Symbol) -> Ident {
    Ident::build(&p.to_string().to_lowercase())
}

pub(crate) fn closure_accessor_name(tcx: TyCtxt, def: DefId, ix: usize) -> Ident {
    let ty_name = item_name(tcx, def, Namespace::TypeNS).to_string().to_lowercase();

    format!("{}_{}", &*ty_name, ix).into()
}

pub(crate) fn variant_accessor_name(
    tcx: TyCtxt,
    def: DefId,
    variant: usize,
    field: usize,
) -> Ident {
    let variant_def = &tcx.adt_def(def).variants()[variant.into()];
    let variant = variant_def;
    format!("{}_{}", variant.name.as_str().to_ascii_lowercase(), variant.fields[field].name).into()
}

pub(crate) fn intty_to_ty(names: &mut CloneMap<'_>, ity: &creusot_rustc::middle::ty::IntTy) -> MlT {
    use creusot_rustc::middle::ty::IntTy::*;
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

pub(crate) fn uintty_to_ty(
    names: &mut CloneMap<'_>,
    ity: &creusot_rustc::middle::ty::UintTy,
) -> MlT {
    use creusot_rustc::middle::ty::UintTy::*;
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

pub(crate) fn floatty_to_ty(
    names: &mut CloneMap<'_>,
    fty: &creusot_rustc::middle::ty::FloatTy,
) -> MlT {
    use creusot_rustc::middle::ty::FloatTy::*;

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
