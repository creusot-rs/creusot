use crate::{
    backend::{Why3Generator, clone_map::Namer, program::IntermediateStmt, ty::translate_ty},
    contracts_items::{get_index_logic, get_int_ty, is_snap_ty},
    ctx::PreMod,
    naming::name,
    translation::traits,
};
use rustc_middle::{
    mir::{ProjectionElem, tcx::PlaceTy},
    ty::{GenericArg, Ty, TyCtxt, TyKind},
};
use rustc_span::Span;
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
pub(crate) struct Focus<'a>(
    Rc<RefCell<Box<dyn FnOnce(Option<&mut Vec<IntermediateStmt>>) -> Exp + 'a>>>,
);

impl<'a> Focus<'a> {
    pub(crate) fn new(f: impl FnOnce(Option<&mut Vec<IntermediateStmt>>) -> Exp + 'a) -> Self {
        Focus(Rc::new(RefCell::new(Box::new(f))))
    }

    pub(crate) fn call(&self, istmts: Option<&mut Vec<IntermediateStmt>>) -> Exp {
        let res = self.0.replace(Box::new(|_| unreachable!()))(istmts);
        let res1 = res.clone();
        let _ = self.0.replace(Box::new(|_| res));
        res1
    }
}

type Constructor<'a> = Box<dyn FnOnce(Option<&mut Vec<IntermediateStmt>>, Exp) -> Exp + 'a>;

pub(crate) fn iter_projections_ty<'tcx, 'a, V: Debug>(
    tcx: TyCtxt<'tcx>,
    proj: &'a [ProjectionElem<V, Ty<'tcx>>],
    place_ty: &'a mut PlaceTy<'tcx>,
) -> impl Iterator<Item = (&'a ProjectionElem<V, Ty<'tcx>>, PlaceTy<'tcx>)> {
    proj.iter().map(move |elem| {
        // Code in pearlite.rs does not insert a projection when seeing
        // a deref of a snapshot. Thus we remove this from the type if a snapshot appears.
        while let TyKind::Adt(d, subst) = place_ty.ty.kind()
            && is_snap_ty(tcx, d.did())
        {
            assert_matches!(place_ty.variant_index, None);
            place_ty.ty = subst.type_at(0);
        }
        let r = (elem, *place_ty);
        *place_ty = projection_ty(*place_ty, tcx, elem);
        r
    })
}

pub(crate) fn projections_to_expr<'tcx, 'a, N: Namer<'tcx>, V: Debug>(
    ctx: &'a Why3Generator<'tcx>,
    names: &'a N,
    mut istmts: Option<&mut Vec<IntermediateStmt>>,
    place_ty: &mut PlaceTy<'tcx>,
    // The term holding the currently 'focused' portion of the place
    mut focus: Focus<'a>,
    mut constructor: Constructor<'a>,
    proj: &'a [ProjectionElem<V, Ty<'tcx>>],
    mut translate_index: impl FnMut(&V) -> Exp,
    span: Span,
) -> (Focus<'a>, Constructor<'a>) {
    for (elem, place_ty) in iter_projections_ty(ctx.tcx, proj, place_ty) {
        // TODO: name hygiene
        match elem {
            ProjectionElem::Deref => {
                let mutable = place_ty.ty.is_mutable_ptr();
                if mutable {
                    let focus1 = focus.clone();
                    focus =
                        Focus::new(move |is| focus.call(is).field(Name::Global(name::current())));
                    constructor = Box::new(move |mut is, t| {
                        let record = Box::new(focus1.call(is.as_deref_mut()));
                        constructor(is, Exp::RecUp {
                            record,
                            updates: Box::new([(Name::Global(name::current()), t)]),
                        })
                    });
                }
            }
            &ProjectionElem::Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) if def.is_enum() => {
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
                    let istmts = istmts.as_deref_mut().unwrap();
                    let args = Box::new([Arg::Term(focus.call(Some(istmts)))]);
                    istmts.push(IntermediateStmt::Call(
                        fields.clone(),
                        Name::local(acc_name),
                        args,
                    ));

                    let foc = Exp::var(fields[ix.as_usize()].as_term().0);
                    focus = Focus::new(|_| foc);

                    constructor = Box::new(move |is, t| {
                        let constr = Exp::var(names.constructor(variant.def_id, subst));
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

                    constructor = Box::new(move |mut is, t| {
                        let updates =
                            Box::new([(Name::local(names.field(def.did(), subst, ix)), t)]);
                        if def.all_fields().count() == 1 {
                            constructor(is, Exp::Record { fields: updates })
                        } else {
                            let record = focus1.call(is.as_deref_mut()).boxed();
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

                    constructor = Box::new(move |mut is, t| {
                        let updates = Box::new([(Name::local(names.tuple_field(args, ix)), t)]);
                        let record = focus1.call(is.as_deref_mut()).boxed();
                        constructor(is, Exp::RecUp { record, updates })
                    });
                }
                TyKind::Closure(id, subst) => {
                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        focus.call(is).field(Name::local(names.field(*id, subst, ix)))
                    });

                    constructor = Box::new(move |mut is, t| {
                        let updates = Box::new([(Name::local(names.field(*id, subst, ix)), t)]);
                        if subst.as_closure().upvar_tys().len() == 1 {
                            constructor(is, Exp::Record { fields: updates })
                        } else {
                            let record = focus1.call(is.as_deref_mut()).boxed();
                            constructor(is, Exp::RecUp { record, updates })
                        }
                    });
                }
                _ => {
                    ctx.dcx().span_bug(span, format!("cannot access field of type {}", place_ty.ty))
                }
            },
            ProjectionElem::Index(ix) => {
                let elt_ty = projection_ty(place_ty, names.tcx(), elem);
                let elt_ty = translate_ty(ctx, names, span, elt_ty.ty);
                let ty = translate_ty(ctx, names, span, place_ty.ty);
                // TODO: Use [_] syntax
                let ix_exp = translate_index(ix);

                let focus1 = focus.clone();
                let elt_ty1 = elt_ty.clone();
                let ix_exp1 = ix_exp.clone();
                focus = Focus::new(move |mut is| {
                    let foc = focus.call(is.as_deref_mut());
                    match is {
                        Some(is) => {
                            let result = Ident::fresh_local("r");
                            is.push(IntermediateStmt::Call(
                                Box::new([Param::Term(result, elt_ty1.clone())]),
                                Name::Global(names.in_pre(PreMod::Slice, "get")),
                                Box::new([Arg::Ty(elt_ty1), Arg::Term(foc), Arg::Term(ix_exp1)]),
                            ));
                            Exp::var(result)
                        }
                        None => {
                            let did = get_index_logic(names.tcx());
                            let int_ty = ctx.type_of(get_int_ty(ctx.tcx)).no_bound_vars().unwrap();
                            let substs = ctx.mk_args(
                                &[names.normalize(ctx, place_ty.ty), int_ty].map(GenericArg::from),
                            );
                            let (did, substs) =
                                traits::resolve_item(ctx.tcx, names.typing_env(), did, substs)
                                    .expect_found(span);
                            Exp::Var(names.item(did, substs)).app([foc, ix_exp1])
                        }
                    }
                });

                constructor = Box::new(move |mut is, t| {
                    let out = Ident::fresh_local("r");
                    let rhs = t;
                    let foc = focus1.call(is.as_deref_mut());
                    is.as_deref_mut().unwrap().push(IntermediateStmt::Call(
                        Box::new([Param::Term(out, ty)]),
                        Name::Global(names.in_pre(PreMod::Slice, "set")),
                        Box::new([
                            Arg::Ty(elt_ty),
                            Arg::Term(foc),
                            Arg::Term(ix_exp),
                            Arg::Term(rhs),
                        ]),
                    ));
                    constructor(is, Exp::var(out))
                });
            }
            ProjectionElem::Downcast(_, _) => {}
            // UNSUPPORTED
            ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::Subtype(_) => {
                ctx.dcx().span_bug(span, format!("Unsupported projection {proj:?}"))
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
    pty.projection_ty_core(tcx, elem, |_, _, ty| ty, |_, ty| ty)
}

/// Generate the ID for a final reborrow of `original_borrow`.
pub(crate) fn borrow_generated_id<'tcx, V: Debug, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    original_borrow: Exp,
    span: Span,
    projections: &[ProjectionElem<V, Ty<'tcx>>],
    mut translate_index: impl FnMut(&V) -> Exp,
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
            ProjectionElem::Index(x) => {
                borrow_id = Exp::qvar(names.in_pre(PreMod::MutBor, "inherit_id"))
                    .app([borrow_id, translate_index(x)]);
            }

            ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. } => {
                // those should inherit a different id instead
                ctx.dcx().span_bug(span, format!("Unsupported projection {proj:?} in reborrow"))
            }
            // Nothing to do
            ProjectionElem::Downcast(..)
            | ProjectionElem::OpaqueCast(_)
            | ProjectionElem::Subtype(_) => {}
        }
    }
    borrow_id
}
