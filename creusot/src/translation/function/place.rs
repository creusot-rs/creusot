use rustc_middle::{
    mir::{Local, Place},
    ty::TyKind,
};
use why3::mlcfg::{
    self,
    Exp::{self, *},
};
use why3::mlcfg::{Pattern::*, Statement::*};

use super::FunctionTranslator;
use crate::ctx::translate_value_id;

impl<'body, 'sess, 'tcx> FunctionTranslator<'body, 'sess, 'tcx> {
    pub fn translate_rplace(&mut self, rhs: &Place<'tcx>) -> Exp {
        self.translate_rplace_inner(rhs.local, rhs.projection)
    }

    // [(P as Some)]   ---> [_1]
    // [(P as Some).0] ---> let Some(a) = [_1] in a
    // [(* P)] ---> * [P]
    fn translate_rplace_inner(
        &mut self,
        loc: Local,
        proj: &[rustc_middle::mir::PlaceElem<'tcx>],
    ) -> Exp {
        let mut inner = self.translate_local(loc).ident().into();
        use rustc_middle::mir::ProjectionElem::*;
        let mut place_ty = Place::ty_from(loc, &[], self.body, self.tcx);

        for elem in proj {
            match elem {
                Deref => {
                    use rustc_hir::Mutability::*;
                    let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                    if mutability == Mut {
                        inner = Current(box inner)
                    }
                }
                Field(ix, _) => match place_ty.ty.kind() {
                    TyKind::Adt(def, _) => {
                        let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                        let variant = &def.variants[variant_id];

                        let mut pat = vec![Wildcard; variant.fields.len()];
                        pat[ix.as_usize()] = VarP("a".into());

                        let tyname = translate_value_id(self.tcx, variant.def_id);

                        inner = Let {
                            pattern: ConsP(tyname, pat),
                            arg: box inner,
                            body: box Var("a".into()),
                        }
                    }
                    TyKind::Tuple(fields) => {
                        let mut pat = vec![Wildcard; fields.len()];
                        pat[ix.as_usize()] = VarP("a".into());

                        inner =
                            Let { pattern: TupleP(pat), arg: box inner, body: box Var("a".into()) }
                    }
                    _ => unreachable!(),
                },
                Downcast(_, _) => {}
                _ => unimplemented!("unimplemented place projection"),
            }
            place_ty = place_ty.projection_ty(self.tcx, *elem);
        }

        inner
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
        let mut stump: &[_] = lhs.projection.clone();

        use rustc_middle::mir::ProjectionElem::*;

        for (proj, elem) in lhs.iter_projections().rev() {
            // twisted stuff
            stump = &stump[0..stump.len() - 1];
            let place_ty = proj.ty(self.body, self.tcx);

            match elem {
                Deref => {
                    use rustc_hir::Mutability::*;

                    let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                    if mutability == Mut {
                        inner = RecUp {
                            record: box self.translate_rplace_inner(lhs.local, stump),
                            label: "current".into(),
                            val: box inner,
                        }
                    }
                }
                Field(ix, _) => match place_ty.ty.kind() {
                    TyKind::Adt(def, _) => {
                        let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());
                        let variant = &def.variants[variant_id];
                        let var_size = variant.fields.len();

                        let field_pats =
                            ('a'..).map(|c| VarP(c.to_string().into())).take(var_size).collect();
                        let mut varexps: Vec<Exp> =
                            ('a'..).map(|c| Var(c.to_string().into())).take(var_size).collect();

                        varexps[ix.as_usize()] = inner;

                        let tyname = translate_value_id(self.tcx, variant.def_id);

                        inner = Let {
                            pattern: ConsP(tyname.clone(), field_pats),
                            arg: box self.translate_rplace_inner(lhs.local, stump),
                            body: box Constructor { ctor: tyname, args: varexps },
                        }
                    }
                    TyKind::Tuple(fields) => {
                        let var_size = fields.len();

                        let field_pats =
                            ('a'..).map(|c| VarP(c.to_string().into())).take(var_size).collect();
                        let mut varexps: Vec<Exp> =
                            ('a'..).map(|c| Var(c.to_string().into())).take(var_size).collect();

                        varexps[ix.as_usize()] = inner;

                        inner = Let {
                            pattern: TupleP(field_pats),
                            arg: box self.translate_rplace_inner(lhs.local, stump),
                            body: box Tuple(varexps),
                        }
                    }
                    _ => unreachable!(),
                },
                Downcast(_, _) => {}
                _ => unimplemented!(),
            }
        }

        let ident = self.translate_local(lhs.local);
        Assign { lhs: ident.ident(), rhs: inner }
    }
}
