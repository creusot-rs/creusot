use std::iter::once;

use crate::{
    backend::Why3Generator,
    contracts_items::{get_builtin, get_int_ty, is_int_ty, is_logic, is_snap_ty, is_trusted},
    ctx::*,
    naming::name,
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{AliasTyKind, GenericArgsRef, Ty, TyCtxt, TyKind, TypingEnv};
use rustc_span::{DUMMY_SP, Span};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::{FloatTy, IntTy, TyKind::*, UintTy};
use why3::{
    Ident, Name,
    coma::{Arg, Defn, Expr, Param, Prototype},
    declaration::{AdtDecl, ConstructorDecl, Decl, FieldDecl, SumRecord, TyDecl},
    exp::{Exp, Trigger},
    ty::Type as MlT,
};

pub(crate) fn translate_ty<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    let ty = names.normalize(ctx, ty);
    match ty.kind() {
        Bool => MlT::qconstructor(name::bool()),
        Char => MlT::qconstructor(names.in_pre(PreMod::Char, "t")),
        Tuple(args) if args.is_empty() => MlT::unit(),
        Tuple(args) if args.len() == 1 => translate_ty(ctx, names, span, args[0]),
        Int(ity) => MlT::qconstructor(names.in_pre(ity_to_prelude(ctx.tcx, *ity), "t")),
        Uint(uty) => MlT::qconstructor(names.in_pre(uty_to_prelude(ctx.tcx, *uty), "t")),
        Float(flty) => MlT::qconstructor(names.in_pre(floatty_to_prelude(*flty), "t")),
        Adt(def, s) if def.is_box() => translate_ty(ctx, names, span, s[0].expect_ty()),
        Adt(def, s) if is_snap_ty(ctx.tcx, def.did()) => {
            // Make sure we create a cycle of dependency if we create a type which is recursive through Snapshot
            // See test should_fail/bug/436_2.rs, and #436
            names.ty(ty);
            translate_ty(ctx, names, span, s[0].expect_ty())
        }
        Adt(def, s) if get_builtin(ctx.tcx, def.did()).is_some() => {
            let cons = MlT::TConstructor(names.ty(ty));
            cons.tapp(s.types().map(|t| translate_ty(ctx, names, span, t)))
        }
        Adt(def, _) if def.is_struct() && def.variant(VariantIdx::ZERO).fields.is_empty() => {
            MlT::unit()
        }
        Adt(def, _) if def.is_enum() && def.variants().is_empty() => MlT::unit(),
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
        Dynamic(_, _, _) => MlT::qconstructor(names.in_pre(PreMod::Opaque, "dyn")),
        Foreign(_) => MlT::qconstructor(names.in_pre(PreMod::Opaque, "foreign")),
        Error(_) => MlT::unit(),
        Closure(..)
        | Adt(..)
        | Tuple(_)
        | Param(_)
        | Alias(AliasTyKind::Opaque | AliasTyKind::Projection, _) => {
            MlT::TConstructor(names.ty(ty))
        }
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

pub(crate) fn translate_closure_ty<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
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

pub(crate) fn translate_tuple_ty<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
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
pub(crate) fn translate_tydecl<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    (did, subst): (DefId, GenericArgsRef<'tcx>),
    typing_env: TypingEnv<'tcx>,
) -> Vec<Decl> {
    // Trusted types (opaque)
    if is_trusted(ctx.tcx, did) {
        let ty_name = names.def_ty(did, subst).to_ident();
        return vec![Decl::TyDecl(TyDecl::Opaque { ty_name, ty_params: Box::new([]) })];
    }

    let adt = ctx.tcx.adt_def(did);
    let ty_name = names.def_ty(did, subst).to_ident();

    let sumrecord = if adt.is_enum() {
        SumRecord::Sum(
            adt.variants()
                .iter()
                .map(|var_def| ConstructorDecl {
                    name: names.constructor(var_def.def_id, subst),
                    fields: var_def
                        .fields
                        .iter()
                        .map(|f| {
                            let ty = f.ty(ctx.tcx, subst);
                            let ty = ctx.normalize_erasing_regions(typing_env, ty);
                            translate_ty(ctx, names, ctx.def_span(f.did), ty)
                        })
                        .collect(),
                })
                .collect(),
        )
    } else {
        assert!(adt.is_struct() || adt.is_union());
        let fields: Box<[_]> = adt
            .variant(VariantIdx::ZERO)
            .fields
            .iter_enumerated()
            .map(|(ix, f)| {
                let name = names.field(did, subst, ix);
                let ty = f.ty(ctx.tcx, subst);
                let ty = ctx.normalize_erasing_regions(typing_env, ty);
                let ty = translate_ty(ctx, names, ctx.def_span(f.did), ty);
                FieldDecl { name, ty }
            })
            .collect();
        if fields.is_empty() {
            return vec![];
        }
        SumRecord::Record(fields)
    };
    vec![Decl::TyDecl(TyDecl::Adt {
        tys: Box::new([AdtDecl { ty_name, ty_params: Box::new([]), sumrecord }]),
    })]
}

pub(crate) fn eliminator<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    variant_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Decl {
    let adt = ctx.adt_def(ctx.parent(variant_id));
    let variant = adt.variant_with_id(variant_id);

    let fields: Box<[_]> = variant
        .fields
        .iter()
        .map(|fld| {
            let id = if fld.name.as_str().as_bytes()[0].is_ascii_digit() {
                &format!("field_{}", fld.name)
            } else {
                fld.name.as_str()
            };
            let ty =
                translate_ty(ctx, names, DUMMY_SP, names.normalize(ctx, fld.ty(ctx.tcx, subst)));
            (Ident::fresh_local(id), ty)
        })
        .collect();

    let field_args: Box<[Param]> =
        fields.iter().cloned().map(|(nm, ty)| Param::Term(nm, ty)).collect();

    let constr = names.constructor(variant_id, subst);
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

pub(crate) fn constructor<'tcx, N: Namer<'tcx>>(
    names: &N,
    fields: Box<[Exp]>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Exp {
    match names.tcx().def_kind(did) {
        DefKind::Variant => {
            let ctor = Name::local(names.constructor(did, subst));
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

pub fn is_int(tcx: TyCtxt, ty: Ty) -> bool {
    if let TyKind::Adt(def, _) = ty.kind() { is_int_ty(tcx, def.did()) } else { false }
}

pub fn int_ty<'tcx, N: Namer<'tcx>>(ctx: &Why3Generator<'tcx>, names: &N) -> MlT {
    let int_id = get_int_ty(ctx.tcx);
    let ty = ctx.type_of(int_id).no_bound_vars().unwrap();
    translate_ty(ctx, names, DUMMY_SP, ty)
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
