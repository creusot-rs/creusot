use crate::{
    backend::{
        program::{floatty_to_prelude, int_to_prelude, uint_to_prelude},
        Why3Generator,
    },
    contracts_items::{get_builtin, get_int_ty, is_int_ty, is_logic, is_trusted},
    ctx::*,
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{AliasTy, AliasTyKind, GenericArgsRef, Ty, TyCtxt, TyKind, TypingEnv};
use rustc_span::{Span, DUMMY_SP};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::{FloatTy, IntTy, TyKind::*, UintTy};
use why3::{
    declaration::{AdtDecl, ConstructorDecl, Decl, FieldDecl, SumRecord, TyDecl},
    exp::{Exp, Trigger},
    ty::Type as MlT,
    Ident, QName,
};

pub(crate) fn translate_ty<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    span: Span,
    ty: Ty<'tcx>,
) -> MlT {
    let ty = names.normalize(ctx, ty);
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
                return translate_ty(ctx, names, span, s[0].expect_ty());
            }

            if is_int(ctx.tcx, ty) {
                names.import_prelude_module(PreludeModule::Int);
                return MlT::Integer;
            }

            if let Some(_) =
                get_builtin(ctx.tcx, def.did()).map(|a| QName::from_string(&a.as_str()))
            {
                let cons = MlT::TConstructor(names.ty(def.did(), s).without_search_path());
                let args: Vec<_> = s.types().map(|t| translate_ty(ctx, names, span, t)).collect();
                MlT::TApp(Box::new(cons), args)
            } else {
                if def.is_struct() && def.variant(VariantIdx::ZERO).fields.is_empty() {
                    MlT::UNIT
                } else {
                    let cons = MlT::TConstructor(names.ty(def.did(), s));
                    MlT::TApp(Box::new(cons), vec![])
                }
            }
        }
        Tuple(ref args) => {
            let tys = (*args).iter().map(|t| translate_ty(ctx, names, span, t)).collect();
            MlT::Tuple(tys)
        }
        Param(_) => MlT::TConstructor(names.ty_param(ty)),
        Alias(AliasTyKind::Projection, pty) => translate_projection_ty(ctx, names, pty),
        Ref(_, ty, borkind) => {
            use rustc_ast::Mutability::*;
            names.import_prelude_module(PreludeModule::Borrow);
            match borkind {
                Mut => MlT::MutableBorrow(Box::new(translate_ty(ctx, names, span, *ty))),
                Not => translate_ty(ctx, names, span, *ty),
            }
        }
        Slice(ty) => {
            names.import_prelude_module(PreludeModule::Slice);
            MlT::TApp(
                Box::new(MlT::TConstructor("slice".into())),
                vec![translate_ty(ctx, names, span, *ty)],
            )
        }
        Array(ty, _) => {
            names.import_prelude_module(PreludeModule::Slice);
            MlT::TApp(
                Box::new(MlT::TConstructor("array".into())),
                vec![translate_ty(ctx, names, span, *ty)],
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
            if is_logic(ctx.tcx, *id) {
                return MlT::Tuple(Vec::new());
            }

            if subst.as_closure().upvar_tys().len() == 0 {
                MlT::Tuple(vec![])
            } else {
                MlT::TConstructor(names.ty(*id, subst))
            }
        }
        FnDef(_, _) =>
        /* FnDef types are effectively singleton types, so it is sound to translate to unit. */
        {
            MlT::Tuple(vec![])
        }
        FnPtr(..) => {
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
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    pty: &AliasTy<'tcx>,
) -> MlT {
    let ty = Ty::new_alias(ctx.tcx, AliasTyKind::Projection, *pty);
    let proj_ty = names.normalize(ctx, ty);
    if let TyKind::Alias(AliasTyKind::Projection, aty) = proj_ty.kind() {
        return MlT::TConstructor(names.ty(aty.def_id, aty.args));
    };
    translate_ty(ctx, names, DUMMY_SP, proj_ty)
}

pub(crate) fn translate_closure_ty<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<TyDecl> {
    let ty_name = names.ty(did, subst).as_ident();
    let closure_subst = subst.as_closure();
    let fields: Vec<_> = closure_subst
        .upvar_tys()
        .iter()
        .enumerate()
        .map(|(ix, uv)| FieldDecl {
            ty: translate_ty(ctx, names, DUMMY_SP, uv),
            name: names.field(did, subst, ix.into()).as_ident(),
        })
        .collect();

    if fields.len() == 0 {
        return None;
    }

    Some(TyDecl::Adt {
        tys: vec![AdtDecl { ty_name, ty_params: vec![], sumrecord: SumRecord::Record(fields) }],
    })
}

// Translate a Rust type declation to an ML one
// Rust tuple-like types are translated as one would expect, to product types in WhyML
// Rust struct types are translated to WhyML records.
//
// Mutually recursive types are translated separately, are later merged by the elaborator
pub(crate) fn translate_tydecl<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    (did, subst): (DefId, GenericArgsRef<'tcx>),
    typing_env: TypingEnv<'tcx>,
) -> Vec<Decl> {
    // Trusted types (opaque)
    if is_trusted(ctx.tcx, did) {
        let ty_name = names.ty(did, subst).as_ident();
        return vec![Decl::TyDecl(TyDecl::Opaque { ty_name, ty_params: vec![] })];
    }

    let adt = ctx.tcx.adt_def(did);
    let ty_name = names.ty(did, subst).as_ident();

    let sumrecord = if adt.is_enum() {
        let mut ml_ty_def = Vec::new();

        for var_def in adt.variants().iter() {
            ml_ty_def.push(ConstructorDecl {
                name: names.constructor(var_def.def_id, subst).as_ident(),
                fields: var_def
                    .fields
                    .iter()
                    .map(|f| {
                        let ty = f.ty(ctx.tcx, subst);
                        let ty = ctx.normalize_erasing_regions(typing_env, ty);
                        translate_ty(ctx, names, ctx.def_span(f.did), ty)
                    })
                    .collect(),
            });
        }

        SumRecord::Sum(ml_ty_def)
    } else {
        assert!(adt.is_struct() || adt.is_union());
        let fields: Vec<_> = adt
            .variant(VariantIdx::ZERO)
            .fields
            .iter_enumerated()
            .map(|(ix, f)| {
                let name = names.field(did, subst, ix).as_ident();
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
    vec![Decl::TyDecl(TyDecl::Adt { tys: vec![AdtDecl { ty_name, ty_params: vec![], sumrecord }] })]
}

pub(crate) fn eliminator<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    variant_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Decl {
    use why3::coma::{self, Arg, Defn, Expr, Param};

    let adt = ctx.adt_def(ctx.parent(variant_id));
    let variant = adt.variant_with_id(variant_id);

    let fields: Vec<_> = variant
        .fields
        .iter()
        .map(|fld| {
            let id = if fld.name.as_str().as_bytes()[0].is_ascii_digit() {
                Ident::build(&format!("field_{}", fld.name))
            } else {
                Ident::build(fld.name.as_str())
            };
            let ty =
                translate_ty(ctx, names, DUMMY_SP, names.normalize(ctx, fld.ty(ctx.tcx, subst)));
            (id, ty)
        })
        .collect();

    let field_args: Vec<coma::Param> =
        fields.iter().cloned().map(|(nm, ty)| Param::Term(nm, ty)).collect();

    let constr = names.constructor(variant_id, subst);
    let cons_test =
        Exp::qvar(constr).app(fields.iter().map(|(nm, _)| Exp::var(nm.clone())).collect());

    let ret = Expr::Symbol("ret".into())
        .app(fields.iter().map(|(nm, _)| Arg::Term(Exp::var(nm.clone()))).collect());

    let good_branch: coma::Defn = coma::Defn {
        name: format!("good").into(),
        writes: vec![],
        params: field_args.clone(),
        body: Expr::Assert(
            Box::new(cons_test.clone().eq(Exp::var("input"))),
            Box::new(Expr::BlackBox(Box::new(ret))),
        ),
    };

    let ty = translate_ty(ctx, names, DUMMY_SP, Ty::new_adt(ctx.tcx, adt, subst));
    let bad_branch = if adt.variants().len() > 1 {
        let fail =
            Expr::BlackBox(Box::new(Expr::Assert(Box::new(Exp::mk_false()), Box::new(Expr::Any))));

        let fields: Vec<_> = fields.iter().cloned().collect();
        let negative_assertion = if fields.is_empty() {
            cons_test.neq(Exp::var("input"))
        } else {
            // TODO: Replace this with a pattern match to generat more readable goals
            Exp::Forall(
                fields,
                vec![Trigger::single(cons_test.clone().ascribe(ty.clone()))],
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

    let input = Param::Term("input".into(), ty);

    let branches = std::iter::once(good_branch).chain(bad_branch).collect();
    Decl::Coma(Defn {
        name: names.eliminator(variant_id, subst).as_ident(),
        writes: vec![],
        params: vec![input, ret_cont],
        body: Expr::Defn(Box::new(Expr::Any), false, branches),
    })
}

pub(crate) fn constructor<'tcx, N: Namer<'tcx>>(
    names: &mut N,
    fields: Vec<Exp>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Exp {
    match names.tcx().def_kind(did) {
        DefKind::Variant => {
            let ctor = names.constructor(did, subst);
            Exp::Constructor { ctor, args: fields }
        }
        DefKind::Closure | DefKind::Struct => {
            if fields.len() == 0 {
                Exp::Tuple(vec![])
            } else {
                let fields = fields
                    .into_iter()
                    .enumerate()
                    .map(|(ix, f)| (names.field(did, subst, ix.into()).as_ident().to_string(), f))
                    .collect();
                Exp::Record { fields }
            }
        }
        _ => unreachable!(),
    }
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
        is_int_ty(tcx, def.did())
    } else {
        false
    }
}

pub fn int_ty<'tcx, N: Namer<'tcx>>(ctx: &mut Why3Generator<'tcx>, names: &mut N) -> MlT {
    let int_id = get_int_ty(ctx.tcx);
    let ty = ctx.type_of(int_id).skip_binder();
    translate_ty(ctx, names, DUMMY_SP, ty)
}
