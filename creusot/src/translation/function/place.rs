use super::{BodyTranslator, LocalIdent};
use crate::{
    ctx::{CloneMap, TranslationCtx},
    translation::{
        function::statement::uint_to_int,
        ty::{closure_accessor_name, variant_accessor_name},
    },
    util::{constructor_qname, item_qname},
};
use creusot_rustc::{
    middle::ty::{TyKind, UintTy},
    smir::mir::{Body, Local, Place},
};
use std::collections::HashMap;
use why3::{
    exp::{
        Exp::{self, *},
        Pattern::*,
    },
    mlcfg::{self, Statement::*},
    QName,
};

impl<'body, 'sess, 'tcx> BodyTranslator<'body, 'sess, 'tcx> {
    pub fn translate_rplace(&mut self, rhs: &Place<'tcx>) -> Exp {
        translate_rplace_inner(
            &mut self.ctx,
            &mut self.names,
            &self.body,
            &self.local_map,
            rhs.local,
            rhs.projection,
        )
    }

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
    pub fn create_assign(&mut self, lhs: &Place<'tcx>, rhs: Exp) -> mlcfg::Statement {
        // Translation happens inside to outside, which means we scan projection elements in reverse
        // building up the inner expression. We start with the RHS expression which is at the deepest
        // level.

        let mut inner = rhs;

        // Each level of the translation needs access to the _previous_ value at this nesting level
        // So we track the path from the root as we traverse, which we call the stump.
        let mut stump: &[_] = lhs.projection;

        use creusot_rustc::smir::mir::ProjectionElem::*;

        for (proj, elem) in lhs.iter_projections().rev() {
            // twisted stuff
            stump = &stump[0..stump.len() - 1];
            let place_ty = proj.ty(self.body, self.tcx);

            match elem {
                Deref => {
                    use creusot_rustc::hir::Mutability::*;

                    let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                    if mutability == Mut {
                        inner = RecUp {
                            record: box translate_rplace_inner(
                                &mut self.ctx,
                                &mut self.names,
                                &self.body,
                                &self.local_map,
                                lhs.local,
                                stump,
                            ),
                            label: "current".into(),
                            val: box inner,
                        }
                    }
                }
                Field(ix, _) => match place_ty.ty.kind() {
                    TyKind::Adt(def, _) => {
                        let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                        let variant = &def.variants()[variant_id];
                        let var_size = variant.fields.len();

                        let field_pats =
                            ('a'..).map(|c| VarP(c.to_string().into())).take(var_size).collect();
                        let mut varexps: Vec<Exp> = ('a'..)
                            .map(|c| Exp::impure_var(c.to_string().into()))
                            .take(var_size)
                            .collect();

                        varexps[ix.as_usize()] = inner;

                        let tyname = constructor_qname(self.tcx, variant);

                        inner = Let {
                            pattern: ConsP(tyname.clone(), field_pats),
                            arg: box translate_rplace_inner(
                                &mut self.ctx,
                                &mut self.names,
                                &self.body,
                                &self.local_map,
                                lhs.local,
                                stump,
                            ),
                            body: box Constructor { ctor: tyname, args: varexps },
                        }
                    }
                    TyKind::Tuple(fields) => {
                        let var_size = fields.len();

                        let field_pats =
                            ('a'..).map(|c| VarP(c.to_string().into())).take(var_size).collect();
                        let mut varexps: Vec<Exp> = ('a'..)
                            .map(|c| Exp::impure_var(c.to_string().into()))
                            .take(var_size)
                            .collect();

                        varexps[ix.as_usize()] = inner;

                        inner = Let {
                            pattern: TupleP(field_pats),
                            arg: box translate_rplace_inner(
                                &mut self.ctx,
                                &mut self.names,
                                &self.body,
                                &self.local_map,
                                lhs.local,
                                stump,
                            ),
                            body: box Tuple(varexps),
                        }
                    }
                    TyKind::Closure(id, subst) => {
                        let count = subst.as_closure().upvar_tys().count();
                        let field_pats =
                            ('a'..).map(|c| VarP(c.to_string().into())).take(count).collect();

                        let mut varexps: Vec<Exp> = ('a'..)
                            .map(|c| Exp::impure_var(c.to_string().into()))
                            .take(count)
                            .collect();

                        varexps[ix.as_usize()] = inner;
                        let mut cons = item_qname(self.tcx, *id);
                        cons.name.capitalize();

                        inner = Let {
                            pattern: ConsP(cons.clone(), field_pats),
                            arg: box translate_rplace_inner(
                                &mut self.ctx,
                                &mut self.names,
                                &self.body,
                                &self.local_map,
                                lhs.local,
                                stump,
                            ),
                            body: box Exp::Constructor { ctor: cons, args: varexps },
                        }
                    }
                    _ => unreachable!(),
                },
                Downcast(_, _) => {}
                Index(ix) => {
                    let set = Exp::impure_qvar(QName::from_string("Seq.set").unwrap());
                    let conv_func = uint_to_int(&UintTy::Usize);
                    let ix_exp = Exp::impure_var(self.translate_local(ix).ident());

                    inner = Call(
                        box set,
                        vec![
                            translate_rplace_inner(
                                &mut self.ctx,
                                &mut self.names,
                                &self.body,
                                &self.local_map,
                                lhs.local,
                                stump,
                            ),
                            conv_func.app_to(ix_exp),
                            inner,
                        ],
                    )
                }
                ConstantIndex { .. } => unimplemented!("ConstantIndex"),
                Subslice { .. } => unimplemented!("Subslice"),
            }
        }

        let ident = self.translate_local(lhs.local);
        Assign { lhs: ident.ident(), rhs: inner }
    }
}

// [(P as Some)]   ---> [_1]
// [(P as Some).0] ---> let Some(a) = [_1] in a
// [(* P)] ---> * [P]
pub(super) fn translate_rplace_inner<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    body: &Body<'tcx>,
    map: &HashMap<Local, Local>,
    loc: Local,
    proj: &[creusot_rustc::middle::mir::PlaceElem<'tcx>],
) -> Exp {
    let mut inner = Exp::impure_var(translate_local(body, map, loc).ident());
    use creusot_rustc::smir::mir::ProjectionElem::*;
    let mut place_ty = Place::ty_from(loc, &[], body, ctx.tcx);

    for elem in proj {
        match elem {
            Deref => {
                use creusot_rustc::hir::Mutability::*;
                let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                if mutability == Mut {
                    inner = Current(box inner)
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                TyKind::Adt(def, _) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                    let variant = &def.variants()[variant_id];

                    ctx.translate_accessor(def.variants()[variant_id].fields[ix.as_usize()].did);
                    let accessor_name =
                        variant_accessor_name(ctx.tcx, def.did(), variant, ix.as_usize());
                    inner = Call(
                        box Exp::impure_qvar(QName {
                            module: vec!["Type".into()],
                            name: accessor_name,
                        }),
                        vec![inner],
                    );
                }
                TyKind::Tuple(fields) => {
                    let mut pat = vec![Wildcard; fields.len()];
                    pat[ix.as_usize()] = VarP("a".into());

                    inner = Let {
                        pattern: TupleP(pat),
                        arg: box inner,
                        body: box Exp::impure_var("a".into()),
                    }
                }
                TyKind::Closure(id, subst) => {
                    let accessor_name = closure_accessor_name(ctx.tcx, *id, ix.as_usize());
                    inner = Call(
                        box Exp::impure_qvar(names.insert(*id, subst).qname_ident(accessor_name)),
                        vec![inner],
                    );
                }
                e => unreachable!("{:?}", e),
            },
            Downcast(_, _) => {}
            Index(ix) => {
                // TODO: Use [_] syntax
                let ix_exp = Exp::impure_var(translate_local(body, map, *ix).ident());
                let conv_func = uint_to_int(&UintTy::Usize);
                inner = Call(
                    box Exp::impure_qvar(QName::from_string("Seq.get").unwrap()),
                    vec![inner, conv_func.app_to(ix_exp)],
                )
            }
            ConstantIndex { .. } => unimplemented!("constant index projection"),
            Subslice { .. } => unimplemented!("subslice projection"),
        }
        place_ty = place_ty.projection_ty(ctx.tcx, *elem);
    }

    inner
}

pub(super) fn translate_local(body: &Body, map: &HashMap<Local, Local>, loc: Local) -> LocalIdent {
    use creusot_rustc::smir::mir::VarDebugInfoContents::Place;
    let debug_info: Vec<_> = body
        .var_debug_info
        .iter()
        .filter(|var_info| match var_info.value {
            Place(p) => p.as_local().map(|l| l == loc).unwrap_or(false),
            _ => false,
        })
        .collect();

    assert!(debug_info.len() <= 1, "expected at most one debug entry for local {:?}", loc);
    let loc = *map.get(&loc).unwrap_or(&loc);
    match debug_info.get(0) {
        Some(info) => LocalIdent::dbg(loc, *info),
        None => LocalIdent::anon(loc),
    }
}
