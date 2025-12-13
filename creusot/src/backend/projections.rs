use crate::{
    backend::{
        Why3Generator,
        clone_map::Namer,
        program::IntermediateStmt,
        ty::{translate_ty, uty_to_prelude},
    },
    contracts_items::Intrinsic,
    ctx::{PreMod, TranslationCtx},
    naming::name,
    translation::{
        pearlite::{PIdent, Pattern, Term},
        traits::TraitResolved,
    },
};
use rustc_abi::VariantIdx;
use rustc_middle::{
    mir::{PlaceTy, ProjectionElem},
    ty::{GenericArg, Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::Span;
use rustc_type_ir::UintTy;
use std::{assert_matches::assert_matches, cell::RefCell, fmt::Debug, rc::Rc};
use why3::{
    Ident, Name,
    coma::{Arg, Param},
    exp::{Constant, Exp},
};

/// The challenge here is correctly construction the expression that assigns deep inside a structure.
/// (_1 as Some) = P      ---> let _1 = P ??
/// (*_1) = P             ---> let _1 = { current = P, .. }
/// (_1.2) = P            ---> let _1 = { _1 with [[2]] = P } (struct)
///                       ---> let _1 = (let Cons(a, b, c) = _1 in Cons(a, b, P)) (tuple)
/// (*_1).1 = P           ---> let _1 = { _1 with current = ({ * _1 with [[1]] = P })}
/// ((*_1) as Some).0 = P ---> let _1 = { _1 with current = (let Some(X) = _1 in Some(P) )}
/// [(_1 as Some).0] = X   ---> let _1 = (let Some(a) = _1 in Some(X))
/// (* (* _1).2) = X ---> let _1 = { _1 with current = { * _1 with current = [(**_1).2 = X] }}

#[derive(Clone)]
pub(crate) struct Focus<'a>(Rc<RefCell<Box<dyn FnOnce(&mut Vec<IntermediateStmt>) -> Exp + 'a>>>);

impl<'a> Focus<'a> {
    pub(crate) fn new(f: impl FnOnce(&mut Vec<IntermediateStmt>) -> Exp + 'a) -> Self {
        Focus(Rc::new(RefCell::new(Box::new(f))))
    }

    pub(crate) fn call(&self, istmts: &mut Vec<IntermediateStmt>) -> Exp {
        let res = self.0.replace(Box::new(|_| unreachable!()))(istmts);
        let res1 = res.clone();
        let _ = self.0.replace(Box::new(|_| res));
        res1
    }
}

type Constructor<'a> = Box<dyn FnOnce(&mut Vec<IntermediateStmt>, Exp) -> Exp + 'a>;

pub(crate) fn iter_projections_ty<'tcx, 'a, V: Debug>(
    ctx: &TranslationCtx<'tcx>,
    proj: &'a [ProjectionElem<V, Ty<'tcx>>],
    place_ty: &'a mut PlaceTy<'tcx>,
) -> impl Iterator<Item = (&'a ProjectionElem<V, Ty<'tcx>>, PlaceTy<'tcx>)> {
    proj.iter().map(move |elem| {
        // Code in pearlite.rs does not insert a projection when seeing
        // a deref of a snapshot. Thus we remove this from the type if a snapshot appears.
        //
        // Note: this is only relevant for place projections in Pearlite terms, for logical
        // reborrowing
        while let TyKind::Adt(d, subst) = place_ty.ty.kind()
            && Intrinsic::Snapshot.is(ctx, d.did())
        {
            assert_matches!(place_ty.variant_index, None);
            place_ty.ty = subst.type_at(0);
        }

        let r = (elem, *place_ty);
        *place_ty = projection_ty(*place_ty, ctx.tcx, elem);
        r
    })
}

pub(crate) fn projections_to_expr<'tcx, 'a>(
    ctx: &'a Why3Generator<'tcx>,
    names: &'a impl Namer<'tcx>,
    istmts: &mut Vec<IntermediateStmt>,
    place_ty: &mut PlaceTy<'tcx>,
    // The term holding the currently 'focused' portion of the place
    mut focus: Focus<'a>,
    mut constructor: Constructor<'a>,
    proj: &'a [ProjectionElem<PIdent, Ty<'tcx>>],
    span: Span,
) -> (Focus<'a>, Constructor<'a>) {
    for (elem, place_ty) in iter_projections_ty(ctx, proj, place_ty) {
        // TODO: name hygiene
        match elem {
            ProjectionElem::Deref => {
                let mutable = place_ty.ty.is_mutable_ptr();
                if mutable {
                    let focus1 = focus.clone();
                    focus =
                        Focus::new(move |is| focus.call(is).field(Name::Global(name::current())));
                    constructor = Box::new(move |is, t| {
                        let record = Box::new(focus1.call(is));
                        constructor(
                            is,
                            Exp::RecUp {
                                record,
                                updates: Box::new([(Name::Global(name::current()), t)]),
                            },
                        )
                    });
                }
            }
            &ProjectionElem::Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) if def.is_enum() || def.is_union() => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let fields: Box<[_]> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            Param::Term(
                                Ident::fresh_local(format!("r{}", f.name)),
                                translate_ty(ctx, names, span, f.ty(names.tcx(), subst)),
                            )
                        })
                        .collect();

                    let acc_name = names.eliminator(variant.def_id, subst);
                    let args = Box::new([Arg::Term(focus.call(istmts))]);
                    istmts.push(IntermediateStmt::Call(
                        fields.clone(),
                        Name::local(acc_name),
                        args,
                        None,
                    ));

                    let foc = Exp::var(fields[ix.as_usize()].as_term().0);
                    focus = Focus::new(|_| foc);

                    constructor = Box::new(move |is, t| {
                        let constr = Exp::var(names.item_ident(variant.def_id, subst));
                        let mut fields: Box<[_]> =
                            fields.into_iter().map(|f| Exp::var(f.as_term().0)).collect();
                        fields[ix.as_usize()] = t;
                        constructor(is, constr.app(fields))
                    });
                }
                TyKind::Adt(def, subst) => {
                    assert!(def.is_struct());

                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(Name::local(names.field(def.did(), subst, ix)))
                    });

                    constructor = Box::new(move |is, t| {
                        let updates =
                            Box::new([(Name::local(names.field(def.did(), subst, ix)), t)]);
                        if def.all_fields().count() == 1 {
                            constructor(is, Exp::Record { fields: updates })
                        } else {
                            let record = focus1.call(is).boxed();
                            constructor(is, Exp::RecUp { record, updates })
                        }
                    })
                }
                TyKind::Tuple(args) if args.len() == 1 => {}
                TyKind::Tuple(args) => {
                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(Name::local(names.tuple_field(args, ix)))
                    });

                    constructor = Box::new(move |is, t| {
                        let updates = Box::new([(Name::local(names.tuple_field(args, ix)), t)]);
                        let record = focus1.call(is).boxed();
                        constructor(is, Exp::RecUp { record, updates })
                    });
                }
                TyKind::Closure(id, subst) => {
                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(Name::local(names.field(*id, subst, ix)))
                    });

                    constructor = Box::new(move |is, t| {
                        let updates = Box::new([(Name::local(names.field(*id, subst, ix)), t)]);
                        if subst.as_closure().upvar_tys().len() == 1 {
                            constructor(is, Exp::Record { fields: updates })
                        } else {
                            let record = focus1.call(is).boxed();
                            constructor(is, Exp::RecUp { record, updates })
                        }
                    });
                }
                _ => {
                    ctx.dcx().span_bug(span, format!("cannot access field of type {}", place_ty.ty))
                }
            },
            ProjectionElem::Index(ix) => {
                let ix = ix.0;
                let elt_ty = projection_ty(place_ty, names.tcx(), elem);
                let elt_ty = translate_ty(ctx, names, span, elt_ty.ty);
                let ty = translate_ty(ctx, names, span, place_ty.ty);

                let focus1 = focus.clone();
                let elt_ty1 = elt_ty.clone();
                focus = Focus::new(move |is| {
                    let foc = focus.call(is);
                    let result = Ident::fresh_local("r");
                    is.push(IntermediateStmt::Call(
                        Box::new([Param::Term(result, elt_ty1.clone())]),
                        Name::Global(names.in_pre(PreMod::Slice, "get")),
                        Box::new([Arg::Ty(elt_ty1), Arg::Term(foc), Arg::Term(Exp::var(ix))]),
                        None,
                    ));
                    Exp::var(result)
                });

                constructor = Box::new(move |is, t| {
                    let out = Ident::fresh_local("r");
                    let rhs = t;
                    let foc = focus1.call(is);
                    is.push(IntermediateStmt::Call(
                        Box::new([Param::Term(out, ty)]),
                        Name::Global(names.in_pre(PreMod::Slice, "set")),
                        Box::new([
                            Arg::Ty(elt_ty),
                            Arg::Term(foc),
                            Arg::Term(Exp::var(ix)),
                            Arg::Term(rhs),
                        ]),
                        None,
                    ));
                    constructor(is, Exp::var(out))
                });
            }
            ProjectionElem::Downcast(_, _) => {}
            // UNSUPPORTED
            ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::UnwrapUnsafeBinder(_) => {
                ctx.dcx().span_bug(span, format!("Unsupported projection {elem:?}"))
            }
        }
    }

    (focus, constructor)
}

pub(crate) fn projection_ty<'tcx, V: Debug>(
    pty: PlaceTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    elem: &ProjectionElem<V, Ty<'tcx>>,
) -> PlaceTy<'tcx> {
    pty.projection_ty_core(tcx, elem, |ty| ty, |_, _, _, ty| ty, |ty| ty)
}

/// Generate the ID for a final reborrow of `original_borrow`.
pub(crate) fn borrow_generated_id<'tcx, V: Debug>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    original_borrow: Exp,
    span: Span,
    projections: &[ProjectionElem<V, Ty<'tcx>>],
    mut translate_index: impl FnMut(&V) -> (Exp, Ty<'tcx>),
) -> Exp {
    let mut borrow_id = Exp::qvar(names.in_pre(PreMod::MutBor, "get_id")).app([original_borrow]);
    for proj in projections {
        match proj {
            ProjectionElem::Deref => {
                // TODO: If this is a deref of a mutable borrow, the id should change !
            }
            ProjectionElem::Field(idx, _) => {
                borrow_id = Exp::qvar(names.in_pre(PreMod::MutBor, "inherit_id"))
                    .app([borrow_id, Exp::Const(Constant::Int(idx.as_u32() as i128 + 1, None))]);
            }
            ProjectionElem::Index(idx) => {
                let (mut idx, idxty) = translate_index(idx);
                if idxty == ctx.types.usize {
                    let qname = names.in_pre(uty_to_prelude(ctx.tcx, UintTy::Usize), "t'int");
                    idx = Exp::qvar(qname).app([idx])
                } else {
                    assert_eq!(idxty, ctx.int_ty());
                }
                borrow_id =
                    Exp::qvar(names.in_pre(PreMod::MutBor, "inherit_id")).app([borrow_id, idx]);
            }
            ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::UnwrapUnsafeBinder(_) => {
                // those should inherit a different id instead
                ctx.dcx().span_bug(span, format!("Unsupported projection {proj:?} in reborrow"))
            }
            // Nothing to do
            ProjectionElem::Downcast(..) | ProjectionElem::OpaqueCast(_) => {}
        }
    }
    borrow_id
}

pub(crate) fn projections_term<'tcx, 'a, V: Debug>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subject: Term<'tcx>,                  // The thing which is projected
    proj: &[ProjectionElem<V, Ty<'tcx>>], // The projections
    exp: impl FnOnce(Term<'tcx>) -> Term<'tcx> + 'a, // What to do with the result of the projection
    default: Option<Term<'tcx>>,          // What to return if the projection fails (sum types)
    mut translate_index: impl FnMut(&V) -> Term<'tcx>,
    span: Span,
) -> Term<'tcx> {
    enum State<'tcx, 'a> {
        Pat(Pattern<'tcx>, Term<'tcx>),
        Trm(Box<dyn FnOnce(Term<'tcx>) -> Term<'tcx> + 'a>),
    }
    use State::*;

    let mut place_ty = PlaceTy::from_ty(subject.ty);
    let mut state = Trm(Box::new(exp));
    for (el, place_ty) in
        iter_projections_ty(ctx, proj, &mut place_ty).collect::<Vec<_>>().into_iter().rev()
    {
        match (el, state) {
            (ProjectionElem::Deref, Pat(pat, t)) => state = Pat(pat.deref(place_ty.ty), t),
            (ProjectionElem::Deref, Trm(trm)) => state = Trm(Box::new(|x| trm(x.deref()))),
            (ProjectionElem::Field(fidx, _), Pat(pat, t))
                if let TyKind::Tuple(tys) = place_ty.ty.kind() =>
            {
                let mut fields: Box<[_]> = tys.iter().map(Pattern::wildcard).collect();
                fields[fidx.as_usize()] = pat;
                state = Pat(Pattern::tuple(fields, place_ty.ty), t)
            }
            (ProjectionElem::Field(fidx, _), Trm(trm))
                if let TyKind::Tuple(tys) = place_ty.ty.kind() =>
            {
                state = Trm(Box::new(move |x| trm(x.proj(*fidx, tys[fidx.as_usize()]))))
            }
            (ProjectionElem::Field(fidx, fty), Trm(trm))
                if let TyKind::Adt(def, _) = place_ty.ty.kind()
                    && def.is_struct() =>
            {
                state = Trm(Box::new(move |x| trm(x.proj(*fidx, *fty))))
            }
            (ProjectionElem::Field(fidx, fty), st) => {
                let (pat, t) = match st {
                    Trm(trm) => {
                        let id = Ident::fresh_local("x");
                        (Pattern::binder(id, *fty), trm(Term::var(id, *fty)))
                    }
                    Pat(pat, t) => (pat, t),
                };
                let variant = place_ty.variant_index.unwrap_or(VariantIdx::ZERO);
                state = Pat(Pattern::constructor(variant, [(*fidx, pat)], place_ty.ty), t)
            }
            (ProjectionElem::Downcast(_, _), st) => state = st,
            (ProjectionElem::Index(idx), st) => {
                let trm = match st {
                    Pat(pat, t) => {
                        let def1 = default.clone().unwrap();
                        Box::new(|x: Term<'tcx>| {
                            let wld = Pattern::wildcard(x.ty);
                            x.match_([(pat, t), (wld, def1)])
                        })
                    }
                    Trm(trm) => trm,
                };
                let idx = translate_index(idx);
                state = Trm(Box::new(move |x| {
                    let did = Intrinsic::IndexLogic.get(ctx);
                    let substs = ctx.mk_args(&[place_ty.ty, idx.ty].map(GenericArg::from));
                    let (did, substs) =
                        TraitResolved::resolve_item(ctx.tcx, typing_env, did, substs)
                            .to_opt(did, substs)
                            .unwrap();
                    trm(Term::call(ctx.tcx, typing_env, did, substs, [x, idx]))
                }))
            }
            (ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. }, _) => {
                ctx.dcx().span_bug(span, "Array and slice patterns are currently not supported")
            }
            (ProjectionElem::OpaqueCast(_) | ProjectionElem::UnwrapUnsafeBinder(_), _) => {
                unreachable!("{el:?} unsupported projection.")
            }
        }
    }

    let subjty = subject.ty;
    match state {
        Pat(pat, t) => subject.match_([(pat, t), (Pattern::wildcard(subjty), default.unwrap())]),
        Trm(trm) => trm(subject),
    }
}
