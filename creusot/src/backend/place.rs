use crate::{backend::Namer, fmir::Place, naming::ident_of};
use rustc_middle::{
    mir::{self, tcx::PlaceTy, ProjectionElem},
    ty::{self, Ty, TyCtxt, TyKind},
};
use rustc_span::Symbol;
use rustc_type_ir::AliasTyKind;
use std::{cell::RefCell, rc::Rc};
use why3::{
    coma::{Arg, Expr, Param},
    exp::{
        Exp::{self, *},
        Pattern::*,
    },
    Ident, QName,
};

use super::program::{IntermediateStmt, LoweringState};

/// Correctly translate an assignment from one place to another. The challenge here is correctly
/// construction the expression that assigns deep inside a structure.
/// (_1 as Some) = P      ---> let _1 = P ??
/// (*_1) = P             ---> let _1 = { current = P, .. }
/// (_1.2) = P            ---> let _1 = { _1 with [[2]] = P } (struct)
///                       ---> let _1 = (let Cons(a, b, c) = _1 in Cons(a, b, P)) (tuple)
/// (*_1).1 = P           ---> let _1 = { _1 with current = ({ * _1 with [[1]] = P })}
/// ((*_1) as Some).0 = P ---> let _1 = { _1 with current = (let Some(X) = _1 in Some(P) )}

/// [(_1 as Some).0] = X   ---> let _1 = (let Some(a) = _1 in Some(X))
/// (* (* _1).2) = X ---> let _1 = { _1 with current = { * _1 with current = [(**_1).2 = X] }}
pub(crate) fn create_assign_inner<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    lhs: &Place<'tcx>,
    rhs: Exp,
    istmts: &mut Vec<IntermediateStmt>,
) {
    let rhs = lplace_to_expr(lower, lhs, rhs, istmts);
    istmts.push(IntermediateStmt::Assign(Ident::build(lhs.local.as_str()), rhs));
}

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

pub(crate) fn projections_to_expr<'tcx, 'a, N: Namer<'tcx>>(
    lower: &'a RefCell<&'a mut LoweringState<'_, 'tcx, N>>,
    istmts: &mut Vec<IntermediateStmt>,
    mut place_ty: PlaceTy<'tcx>,
    // The term holding the currently 'focused' portion of the place
    mut focus: Focus<'a>,
    mut constructor: Constructor<'a>,
    proj: &'a [mir::ProjectionElem<Symbol, Ty<'tcx>>],
) -> (PlaceTy<'tcx>, Focus<'a>, Constructor<'a>) {
    for elem in proj {
        use rustc_middle::mir::ProjectionElem::*;
        // TODO: name hygiene
        match elem {
            Deref => {
                let mutable = place_ty.ty.is_mutable_ptr();
                if mutable {
                    let focus1 = focus.clone();
                    focus = Focus::new(move |is| focus.call(is).field("current"));
                    constructor = Box::new(move |is, t| {
                        let record = Box::new(focus1.call(is));
                        constructor(is, RecUp { record, updates: vec![("current".into(), t)] })
                    });
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, subst) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];
                    let fields: Vec<_> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            let low = &mut *lower.borrow_mut();
                            Param::Term(
                                low.fresh_from(format!("r{}", f.name)),
                                low.ty(f.ty(low.ctx.tcx, subst)),
                            )
                        })
                        .collect();

                    let projections = lower.borrow_mut().ctx.projections_in_ty(def.did()).to_vec();
                    let mut ty_projections = Vec::new();
                    for p in projections {
                        let low = &mut *lower.borrow_mut();
                        let n = low.names.normalize(&low.ctx, p);
                        let ty = low
                            .ty(low.ctx.mk_ty_from_kind(TyKind::Alias(AliasTyKind::Projection, n)));
                        ty_projections.push(ty);
                    }
                    let params = subst
                        .iter()
                        .flat_map(|ty| ty.as_type())
                        .map(|ty| lower.borrow_mut().ty(ty))
                        .chain(ty_projections)
                        .map(Arg::Ty)
                        .chain(std::iter::once(Arg::Term(focus.call(istmts))))
                        .collect();
                    let acc_name = lower.borrow_mut().names.eliminator(variant.def_id, subst);
                    istmts.push(IntermediateStmt::Call(
                        fields.clone(),
                        Expr::Symbol(acc_name),
                        params,
                    ));

                    let foc = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    focus = Focus::new(|_| foc);

                    constructor = Box::new(|is, t| {
                        let constr =
                            Exp::qvar(lower.borrow_mut().names.constructor(variant.def_id, subst));
                        let mut fields: Vec<_> =
                            fields.into_iter().map(|f| Exp::var(f.as_term().0.clone())).collect();
                        fields[ix.as_usize()] = t;
                        // TODO: Only emit type if the constructor would otherwise be ambiguous
                        constructor(is, constr.app(fields))
                    });
                }
                TyKind::Tuple(fields) => {
                    let focus1 = focus.clone();

                    focus = Focus::new(move |is| {
                        let var = lower.borrow_mut().fresh_from("r");
                        let mut pat = vec![Wildcard; fields.len()];
                        pat[ix.as_usize()] = VarP(var.clone());
                        Let {
                            pattern: TupleP(pat.clone()),
                            arg: Box::new(focus.call(is)),
                            body: Box::new(Exp::var(var)),
                        }
                    });

                    constructor = Box::new(move |is, t| {
                        let var_names: Vec<_> =
                            fields.iter().map(|_| lower.borrow_mut().fresh_from("r")).collect();

                        let mut field_pats =
                            var_names.clone().into_iter().map(VarP).collect::<Vec<_>>();
                        field_pats[ix.as_usize()] = Wildcard;

                        let mut varexps = var_names.into_iter().map(Exp::var).collect::<Vec<_>>();
                        varexps[ix.as_usize()] = t;

                        let tuple = Let {
                            pattern: TupleP(field_pats),
                            arg: Box::new(focus1.call(is)),
                            body: Box::new(Exp::Tuple(varexps)),
                        };

                        constructor(is, tuple)
                    });
                }
                TyKind::Closure(id, subst) => {
                    let acc_name = lower.borrow_mut().names.eliminator(*id, subst);
                    let upvars = subst.as_closure().upvar_tys();
                    let field_names: Vec<_> =
                        upvars.iter().map(|_| lower.borrow_mut().fresh_from("r")).collect();

                    let fields: Vec<_> = field_names
                        .iter()
                        .cloned()
                        .zip(upvars)
                        .map(|(id, ty)| Param::Term(id, lower.borrow_mut().ty(ty)))
                        .collect();
                    let params = subst
                        .as_closure()
                        .parent_args()
                        .iter()
                        .flat_map(|arg| arg.as_type())
                        .map(|ty| lower.borrow_mut().ty(ty))
                        .map(Arg::Ty)
                        .chain(std::iter::once(Arg::Term(focus.call(istmts))))
                        .collect();
                    istmts.push(IntermediateStmt::Call(
                        fields.clone(),
                        Expr::Symbol(acc_name),
                        params,
                    ));

                    let foc = Exp::var(fields[ix.as_usize()].as_term().0.clone());
                    focus = Focus::new(|_| foc);

                    constructor = Box::new(|is, t| {
                        let constr = Exp::qvar(lower.borrow_mut().names.constructor(*id, subst));
                        let mut fields: Vec<_> =
                            field_names.into_iter().map(|f| Exp::var(f)).collect();
                        fields[ix.as_usize()] = t;
                        // TODO: Only emit type if the constructor would otherwise be ambiguous
                        constructor(is, constr.app(fields))
                    });
                }
                _ => todo!("place: {:?}", place_ty.ty.kind()),
            },
            Index(ix) => {
                let elt_ty = projection_ty(place_ty, lower.borrow().ctx.tcx, *elem);
                let elt_ty = lower.borrow_mut().ty(elt_ty.ty);
                let ty = lower.borrow_mut().ty(place_ty.ty);
                // TODO: Use [_] syntax
                let ix_exp = Exp::var(Ident::build(ix.as_str()));

                let focus1 = focus.clone();
                let elt_ty1 = elt_ty.clone();
                let ix_exp1 = ix_exp.clone();
                focus = Focus::new(move |is| {
                    let result = lower.borrow_mut().fresh_from("r");
                    let foc = focus.call(is);
                    is.push(IntermediateStmt::Call(
                        vec![Param::Term(result.clone(), elt_ty1.clone())],
                        Expr::Symbol(QName::from_string("Slice.get")),
                        vec![Arg::Ty(elt_ty1), Arg::Term(foc), Arg::Term(ix_exp1)],
                    ));

                    Exp::qvar(result.into())
                });

                constructor = Box::new(move |is, t| {
                    let out = lower.borrow_mut().fresh_from("r");
                    let rhs = t;
                    let foc = focus1.call(is);

                    is.push(IntermediateStmt::Call(
                        vec![Param::Term(out.clone(), ty)],
                        Expr::Symbol(QName::from_string("Slice.set")),
                        vec![Arg::Ty(elt_ty), Arg::Term(foc), Arg::Term(ix_exp), Arg::Term(rhs)],
                    ));
                    constructor(is, Exp::qvar(out.into()))
                });
            }
            Downcast(_, _) => {}
            // UNSUPPORTED
            ConstantIndex { .. } => todo!(),
            Subslice { .. } => todo!(),
            OpaqueCast(_) => todo!(),
            Subtype(_) => todo!(),
        }
        place_ty = projection_ty(place_ty, lower.borrow().ctx.tcx, *elem);
    }

    (place_ty, focus, constructor)
}

pub(crate) fn rplace_to_expr<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    pl: &Place<'tcx>,
    istmts: &mut Vec<IntermediateStmt>,
) -> Exp {
    let place_ty = PlaceTy::from_ty(lower.locals[&pl.local].ty);
    let lower = RefCell::new(lower);
    let (_, rhs, _) = projections_to_expr(
        &lower,
        istmts,
        place_ty,
        Focus::new(|_| Exp::var(ident_of(pl.local))),
        Box::new(|_, _| unreachable!()),
        &pl.projection,
    );
    rhs.call(istmts)
}

fn lplace_to_expr<'tcx, N: Namer<'tcx>>(
    lower: &mut LoweringState<'_, 'tcx, N>,
    pl: &Place<'tcx>,
    rhs: Exp,
    istmts: &mut Vec<IntermediateStmt>,
) -> Exp {
    let place_ty = PlaceTy::from_ty(lower.locals[&pl.local].ty);
    let lower = RefCell::new(lower);
    let (_, _, constructor) = projections_to_expr(
        &lower,
        istmts,
        place_ty,
        Focus::new(|_| Exp::var(ident_of(pl.local))),
        Box::new(|_, x| x),
        &pl.projection,
    );

    constructor(istmts, rhs)
}

pub fn projection_ty<'tcx>(
    pty: PlaceTy<'tcx>,
    tcx: TyCtxt<'tcx>,
    elem: ProjectionElem<Symbol, Ty<'tcx>>,
) -> PlaceTy<'tcx> {
    pty.projection_ty_core(tcx, ty::ParamEnv::empty(), &elem, |_, _, ty| ty, |_, ty| ty)
}
