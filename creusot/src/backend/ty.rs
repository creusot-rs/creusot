use std::iter::once;

use crate::{
    backend::{Why3Generator, dependency::Dependency},
    contracts_items::{Intrinsic, get_builtin, is_logic, is_opaque},
    ctx::*,
    naming::{field_name, name},
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{AdtDef, AliasTyKind, GenericArgsRef, Ty, TyCtxt, TyKind};
use rustc_span::{DUMMY_SP, Span};
use rustc_type_ir::{FloatTy, IntTy, TyKind::*, UintTy};
use why3::{
    Ident, Name,
    coma::{Arg, Defn, Expr, Param, Prototype},
    declaration::{AdtDecl, ConstructorDecl, Decl, FieldDecl, SumRecord, TyDecl, Use},
    exp::{Exp, Trigger},
    ty::Type as MlT,
};

#[derive(PartialEq, Eq, Debug)]
pub enum AdtKind<'tcx> {
    Opaque { always: bool },           // An opaque type for the current context
    Enum,                              // A transparent enum
    Struct { partially_opaque: bool }, // A struct, with potentially some opaque fields
    Unit,                              // Adt with only one element
    Empty,                             // Empty Adt
    Snapshot(Ty<'tcx>),                // Snapshot<T>
    Ghost(Ty<'tcx>),                   // Ghost<T>
    Namespace,                         // Namespace
    Box(Ty<'tcx>),                     // Box<T>
    Builtin(Box<[Ty<'tcx>]>),          // A type directly defined in Why3
}

pub(crate) fn classify_adt<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    scope: DefId,
    def: AdtDef<'tcx>,
    subst: GenericArgsRef<'tcx>,
) -> AdtKind<'tcx> {
    match ctx.intrinsic(def.did()) {
        Intrinsic::Snapshot => return AdtKind::Snapshot(subst[0].expect_ty()),
        Intrinsic::Ghost => return AdtKind::Ghost(subst[0].expect_ty()),
        Intrinsic::Namespace => return AdtKind::Namespace,
        _ => (),
    }
    if def.is_union() {
        AdtKind::Opaque { always: true }
    } else if def.is_box() {
        AdtKind::Box(subst[0].expect_ty())
    } else if get_builtin(ctx.tcx, def.did()).is_some() {
        AdtKind::Builtin(subst.types().collect())
    } else if is_opaque(ctx.tcx, def.did()) {
        AdtKind::Opaque { always: true }
    } else if def.is_enum() && def.variants().is_empty() {
        AdtKind::Empty
    } else if def.is_struct() && def.non_enum_variant().fields.is_empty() {
        AdtKind::Unit
    } else if def.is_enum() {
        AdtKind::Enum
    } else if def
        .non_enum_variant()
        .fields
        .iter()
        .all(|f| !f.vis.is_accessible_from(scope, ctx.tcx))
    {
        AdtKind::Opaque { always: false }
    } else {
        AdtKind::Struct {
            partially_opaque: !def
                .non_enum_variant()
                .fields
                .iter()
                .all(|f| f.vis.is_accessible_from(scope, ctx.tcx)),
        }
    }
}

pub(crate) fn translate_ty<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    let ty = names.normalize(ty);
    match ty.kind() {
        Bool => bool(),
        Char => MlT::qconstructor(names.in_pre(PreMod::Char, "t")),
        Tuple(args) if args.is_empty() => MlT::unit(),
        Tuple(args) if args.len() == 1 => translate_ty(ctx, names, span, args[0]),
        Int(ity) => MlT::qconstructor(names.in_pre(ity_to_prelude(ctx.tcx, *ity), "t")),
        Uint(uty) => MlT::qconstructor(names.in_pre(uty_to_prelude(ctx.tcx, *uty), "t")),
        Float(flty) => MlT::qconstructor(names.in_pre(floatty_to_prelude(*flty), "t")),
        Adt(def, s) => match classify_adt(ctx, names.source_id(), *def, s) {
            AdtKind::Opaque { .. }
            | AdtKind::Enum
            | AdtKind::Struct { .. }
            | AdtKind::Namespace => MlT::TConstructor(names.ty(ty)),
            AdtKind::Unit | AdtKind::Empty => MlT::unit(),
            AdtKind::Ghost(ty) | AdtKind::Box(ty) => translate_ty(ctx, names, span, ty),
            AdtKind::Snapshot(ty_inner) => {
                // Make sure we create a cycle of dependency if we create a type which is recursive through Snapshot
                // See test should_fail/bug/436_2.rs, and #436
                names.ty(ty);
                translate_ty(ctx, names, span, ty_inner)
            }
            AdtKind::Builtin(tys) => {
                let cons = MlT::TConstructor(names.ty(ty));
                cons.tapp(tys.iter().map(|t| translate_ty(ctx, names, span, *t)))
            }
        },
        Ref(_, ty, borkind) => {
            use rustc_ast::Mutability::*;
            match borkind {
                Mut => MlT::qconstructor(names.in_pre(PreMod::MutBor, "t"))
                    .tapp([translate_ty(ctx, names, span, *ty)]),
                Not => translate_ty(ctx, names, span, *ty),
            }
        }
        Slice(ty) => MlT::qconstructor(names.in_pre(PreMod::Slice, "slice"))
            .tapp([translate_ty(ctx, names, span, *ty)]),
        Array(ty, _) => MlT::qconstructor(names.in_pre(PreMod::Slice, "array"))
            .tapp([translate_ty(ctx, names, span, *ty)]),
        Str => MlT::qconstructor(name::string()),
        Never => MlT::unit(),
        RawPtr(_, _) => MlT::qconstructor(names.in_pre(PreMod::Opaque, "ptr")),
        Closure(id, subst)
            if is_logic(ctx.tcx, *id) || subst.as_closure().upvar_tys().is_empty() =>
        {
            MlT::unit()
        }
        FnDef(_, _) => MlT::unit(), /* FnDef types are effectively singleton types, so it is sound to translate to unit. */
        FnPtr(..) => MlT::qconstructor(names.in_pre(PreMod::Opaque, "ptr")),
        Foreign(_) => MlT::qconstructor(names.in_pre(PreMod::Opaque, "foreign")),
        Error(_) => MlT::unit(),
        Closure(..)
        | Tuple(_)
        | Param(_)
        | Dynamic(_, _)
        | Alias(AliasTyKind::Opaque | AliasTyKind::Projection, _) => {
            MlT::TConstructor(names.ty(ty))
        }
        _ => ctx.crash_and_error(span, format!("unsupported type {:?}", ty)),
    }
}

pub(crate) fn translate_closure_ty<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Vec<Decl> {
    let ty_name = names.def_ty(did, subst).to_ident();
    let closure_subst = subst.as_closure();
    let fields: Box<[_]> = closure_subst
        .upvar_tys()
        .iter()
        .enumerate()
        .map(|(ix, uv)| FieldDecl {
            ty: translate_ty(ctx, names, DUMMY_SP, uv),
            name: names.field(did, subst, ix.into()),
        })
        .collect();

    if fields.is_empty() {
        return vec![];
    }

    vec![Decl::TyDecl(TyDecl::Adt {
        tys: Box::new([AdtDecl {
            ty_name,
            ty_params: Box::new([]),
            sumrecord: SumRecord::Record(fields),
        }]),
    })]
}

pub(crate) fn translate_tuple_ty<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let TyKind::Tuple(args) = ty.kind() else { unreachable!() };
    assert!(args.len() > 1);
    let fields: Box<[_]> = args
        .iter()
        .enumerate()
        .map(|(ix, ty)| FieldDecl {
            ty: translate_ty(ctx, names, DUMMY_SP, ty),
            name: names.tuple_field(args, ix.into()),
        })
        .collect();

    vec![Decl::TyDecl(TyDecl::Adt {
        tys: Box::new([AdtDecl {
            ty_name: names.ty(ty).to_ident(),
            ty_params: Box::new([]),
            sumrecord: SumRecord::Record(fields),
        }]),
    })]
}

// Translate a Rust type declation to an ML one
// Rust tuple-like types are translated as one would expect, to product types in WhyML
// Rust struct types are translated to WhyML records.
//
// Mutually recursive types are translated separately, are later merged by the elaborator
pub(crate) fn translate_adtdecl<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let TyKind::Adt(def, subst) = ty.kind() else { unreachable!() };
    match classify_adt(ctx, names.source_id(), *def, subst) {
        AdtKind::Namespace => {
            // Special treatment for the `Namespace` type: we must generate it after collecting all the possible variants.
            ctx.used_namespaces.set(true);
            vec![]
        }
        AdtKind::Builtin(tys) => {
            for ty in tys {
                translate_ty(ctx, names, DUMMY_SP, ty);
            }
            if let Kind::UsedBuiltin(qname) = names.dependency(Dependency::Type(ty))
                && !qname.module.is_empty()
            {
                vec![Decl::UseDecls(Box::new([Use { name: qname.module.clone(), export: false }]))]
            } else {
                vec![]
            }
        }
        AdtKind::Snapshot(ty) => {
            // Make sure we introduce a dependency, to create a cycle if we are recursing through Snapshot
            translate_ty(ctx, names, DUMMY_SP, ty);
            vec![]
        }
        AdtKind::Opaque { .. } => {
            let ty_name = names.def_ty(def.did(), subst).to_ident();
            vec![Decl::TyDecl(TyDecl::Opaque { ty_name, ty_params: Box::new([]) })]
        }
        AdtKind::Enum => {
            let ty_name = names.def_ty(def.did(), subst).to_ident();
            let sumrecord = SumRecord::Sum(
                def.variants()
                    .iter()
                    .map(|var_def| ConstructorDecl {
                        name: names.item_ident(var_def.def_id, subst),
                        fields: var_def
                            .fields
                            .iter()
                            .map(|f| {
                                let ty = ctx.normalize_erasing_regions(
                                    names.typing_env(),
                                    f.ty(ctx.tcx, subst),
                                );
                                translate_ty(ctx, names, ctx.def_span(f.did), ty)
                            })
                            .collect(),
                    })
                    .collect(),
            );
            vec![Decl::TyDecl(TyDecl::Adt {
                tys: Box::new([AdtDecl { ty_name, ty_params: Box::new([]), sumrecord }]),
            })]
        }
        AdtKind::Struct { partially_opaque } => {
            let ty_name = names.def_ty(def.did(), subst).to_ident();

            let fields: Box<[_]> = def
                .non_enum_variant()
                .fields
                .iter_enumerated()
                .filter(|f| f.1.vis.is_accessible_from(names.source_id(), ctx.tcx))
                .map(|(ix, f)| {
                    let ty =
                        ctx.normalize_erasing_regions(names.typing_env(), f.ty(ctx.tcx, subst));
                    FieldDecl {
                        name: names.field(def.did(), subst, ix),
                        ty: translate_ty(ctx, names, ctx.def_span(f.did), ty),
                    }
                })
                .chain(partially_opaque.then(|| {
                    let name = names.private_fields(def.did(), subst);
                    FieldDecl { name, ty: MlT::TConstructor(Name::local(name)) }
                }))
                .collect();
            assert!(!fields.is_empty());
            vec![Decl::TyDecl(TyDecl::Adt {
                tys: Box::new([AdtDecl {
                    ty_name,
                    ty_params: Box::new([]),
                    sumrecord: SumRecord::Record(fields),
                }]),
            })]
        }
        AdtKind::Unit | AdtKind::Empty | AdtKind::Box(_) | AdtKind::Ghost(_) => {
            unreachable!("{ty:?}")
        }
    }
}

pub(crate) fn eliminator<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    variant_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Decl {
    let adt = ctx.adt_def(ctx.parent(variant_id));
    let variant = adt.variant_with_id(variant_id);

    let fields: Box<[_]> = variant
        .fields
        .iter()
        .map(|fld| {
            let ty = translate_ty(ctx, names, DUMMY_SP, names.normalize(fld.ty(ctx.tcx, subst)));
            (Ident::fresh_local(&field_name(fld.name.as_str())), ty)
        })
        .collect();

    let field_args: Box<[Param]> =
        fields.iter().cloned().map(|(nm, ty)| Param::Term(nm, ty)).collect();

    let constr = names.item_ident(variant_id, subst);
    let cons_test = Exp::var(constr).app(fields.iter().map(|(nm, _)| Exp::var(*nm)));

    let ret_ident = Ident::fresh_local("ret");
    let good_ident = Ident::fresh_local("good");
    let bad_ident = Ident::fresh_local("bad");
    let input_ident = Ident::fresh_local("input");
    let ret = Expr::var(ret_ident).app(fields.iter().map(|(nm, _)| Arg::Term(Exp::var(*nm))));

    let good_branch: Defn = Defn {
        prototype: Prototype { name: good_ident, attrs: vec![], params: field_args.clone() },
        body: Expr::assert(cons_test.clone().eq(Exp::var(input_ident)), ret.black_box()),
    };

    let ty = translate_ty(ctx, names, DUMMY_SP, Ty::new_adt(ctx.tcx, adt, subst));
    let bad_branch = if adt.variants().len() > 1 {
        let fail = Expr::assert(Exp::mk_false(), Expr::Any).black_box();

        // TODO: Replace this with a pattern match to generat more readable goals
        let negative_assertion = Exp::forall_trig(
            fields.clone(),
            [Trigger::single(cons_test.clone().ascribe(ty.clone()))],
            cons_test.neq(Exp::var(input_ident)),
        );
        Some(Defn::simple(bad_ident, Expr::assert(negative_assertion, fail)))
    } else {
        None
    };

    let ret_cont = Param::Cont(ret_ident, Box::new([]), field_args);

    let input = Param::Term(input_ident, ty);

    let branches = once(good_branch).chain(bad_branch).collect();
    Decl::Coma(Defn {
        prototype: Prototype {
            name: names.eliminator(variant_id, subst),
            params: Box::new([input, ret_cont]),
            attrs: vec![],
        },
        body: Expr::Defn(Box::new(Expr::Any), false, branches),
    })
}

pub(crate) fn constructor<'tcx>(
    names: &impl Namer<'tcx>,
    fields: Box<[Exp]>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Exp {
    match names.tcx().def_kind(did) {
        DefKind::Variant => {
            let ctor = Name::local(names.item_ident(did, subst));
            Exp::Constructor { ctor, args: fields }
        }
        DefKind::Closure | DefKind::Struct => {
            if fields.is_empty() {
                Exp::unit()
            } else {
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(ix, f)| (Name::local(names.field(did, subst, ix.into())), f))
                    .collect();
                Exp::Record { fields }
            }
        }
        _ => unreachable!(),
    }
}

pub(crate) fn ity_to_prelude(tcx: TyCtxt, ity: IntTy) -> PreMod {
    match ity.normalize(tcx.sess.target.pointer_width) {
        IntTy::Isize => unreachable!(),
        IntTy::I8 => PreMod::Int8,
        IntTy::I16 => PreMod::Int16,
        IntTy::I32 => PreMod::Int32,
        IntTy::I64 => PreMod::Int64,
        IntTy::I128 => PreMod::Int128,
    }
}

pub(crate) fn uty_to_prelude(tcx: TyCtxt, uty: UintTy) -> PreMod {
    match uty.normalize(tcx.sess.target.pointer_width) {
        UintTy::Usize => unreachable!(),
        UintTy::U8 => PreMod::UInt8,
        UintTy::U16 => PreMod::UInt16,
        UintTy::U32 => PreMod::UInt32,
        UintTy::U64 => PreMod::UInt64,
        UintTy::U128 => PreMod::UInt128,
    }
}

pub(crate) fn floatty_to_prelude(fty: FloatTy) -> PreMod {
    match fty {
        FloatTy::F32 => PreMod::Float32,
        FloatTy::F64 => PreMod::Float64,
        FloatTy::F16 | FloatTy::F128 => todo!("unsupported: {fty:?}"),
    }
}

pub fn ty_to_prelude(tcx: TyCtxt<'_>, ty: &TyKind) -> PreMod {
    match ty {
        TyKind::Int(ity) => ity_to_prelude(tcx, *ity),
        TyKind::Uint(uty) => uty_to_prelude(tcx, *uty),
        TyKind::Float(fty) => floatty_to_prelude(*fty),
        TyKind::Bool => PreMod::Bool,
        TyKind::Char => PreMod::Char,
        _ => unreachable!("non-primitive type {ty:?}"),
    }
}

pub fn bool() -> MlT {
    MlT::qconstructor(name::bool())
}

pub fn int<'tcx>(ctx: &Why3Generator<'tcx>, names: &impl Namer<'tcx>) -> MlT {
    translate_ty(ctx, names, DUMMY_SP, ctx.int_ty())
}
