#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![register_tool(wprust)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_span;

use rustc_hir::def::CtorKind;
use rustc_middle::{
    mir::{Body, Local, Place, ProjectionElem::*},
    ty::TyCtxt,
};
use rustc_span::{symbol::Ident, Symbol};
use Projection::*;

fn main() {
    println!("Hello, world!");
}

#[derive(Clone)]
enum Projection {
    MutDeref,
    FieldAccess {
        ctor: Symbol,
        ix: usize,
        size: usize,
        field: Ident,
        kind: CtorKind,
    },
    TupleAccess {
        size: usize,
        ix: usize,
    },
    Down {
        ctor: Symbol,
    },
}

#[derive(Clone)]
pub struct MirPlace {
    local: Local,
    proj: Vec<Projection>,
}

pub fn why_from_place<'tcx>(tcx: TyCtxt<'tcx>, decls: Body<'tcx>, place: Place<'tcx>) -> MirPlace {
    let mut place_ty = place.ty(&decls, tcx);

    // TODO: Use a more appropriate type than Vec<ProjElem>
    let mut res_proj = Vec::new();

    for proj in place.projection.iter() {
        match proj {
            Deref => {
                match place_ty
                    .ty
                    .builtin_deref(false)
                    .expect("not raw pointer")
                    .mutbl
                {
                    rustc_hir::Mutability::Mut => {
                        res_proj.push(MutDeref);
                    }
                    rustc_hir::Mutability::Not => {
                        // Since in the translation [&T] ::= [T], we drop any projections for immutable deref
                    }
                }
            }
            Field(ix, var) => match place_ty.ty.kind() {
                rustc_middle::ty::TyKind::Adt(def, _) => {
                    let variant = &def.variants[place_ty.variant_index.unwrap()];
                    let field = variant.fields[ix.as_usize()].ident;

                    res_proj.push(FieldAccess {
                        ctor: variant.ident.name,
                        ix: ix.as_usize(),
                        size: variant.fields.len(),
                        field,
                        kind: variant.ctor_kind,
                    });
                }
                rustc_middle::ty::TyKind::Tuple(fields) => res_proj.push(TupleAccess {
                    size: fields.len(),
                    ix: ix.as_usize(),
                }),
                _ => {
                    panic!("accessing field on unexpected tykind");
                }
            },
            Downcast(Some(symbol), _) => res_proj.push(Down { ctor: symbol }),
            Downcast(None, _) => {
                panic!("downcast projection with no symbol");
            }
            _ => {
                panic!("unsupported place projection");
            }
        }
        place_ty = place_ty.projection_ty(tcx, proj);
    }

    return MirPlace {
        local: place.local,
        proj: res_proj,
    };
}

pub enum MlCfgExp {
    Current(Box<MlCfgExp>),
    Final(Box<MlCfgExp>),
    Local(Local),
    Let {
        pattern: MlCfgPattern,
        arg: Box<MlCfgExp>,
        body: Box<MlCfgExp>,
    },
    Var(String),
    RecUp {
        record: Box<MlCfgExp>,
        label: String,
        val: Box<MlCfgExp>,
    },
    Tuple(Vec<MlCfgExp>),
    Constructor {
        ctor: String,
        args: Vec<MlCfgExp>,
    },
}

#[derive(Clone)]
pub enum MlCfgPattern {
    Wildcard,
    VarP(String),
    TupleP(Vec<MlCfgPattern>),
    ConsP(String, Vec<MlCfgPattern>),
    RecP(String, String),
}
use MlCfgExp::*;
use MlCfgPattern::*;

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
pub fn handle_assign<'tcx>(tcx: TyCtxt<'tcx>, lhs: MirPlace, rhs: MirPlace) {
    // Translation happens inside to outside, which means we scan projection elements in reverse
    // building up the inner expression. We start with the RHS expression which is at the deepest
    // level.
    let mut inner = rhs_to_why_exp(&rhs);
    // The stump represents the projection up to the element being translated
    let mut stump = lhs.clone();
    for proj in lhs.proj.iter().rev() {
        match proj {
            MutDeref => {
                inner = RecUp {
                    record: box rhs_to_why_exp(&stump),
                    label: "current".into(),
                    val: box inner,
                }
            }
            FieldAccess {
                ctor,
                ix,
                size,
                field,
                kind,
            } => match kind {
                CtorKind::Fn => {
                    let varpats = ('a'..).map(|c| VarP(c.to_string())).take(*size).collect();
                    let mut varexps: Vec<MlCfgExp> =
                        ('a'..).map(|c| Var(c.to_string())).take(*size).collect();
                    varexps[*ix] = inner;

                    inner = Let {
                        pattern: ConsP(ctor.to_string(), varpats),
                        arg: box rhs_to_why_exp(&stump),
                        body: box Constructor {
                            ctor: ctor.to_string(),
                            args: varexps,
                        },
                    }
                }
                CtorKind::Const => unimplemented!(),
                CtorKind::Fictive => {
                    inner = RecUp {
                        record: box rhs_to_why_exp(&stump),
                        label: field.to_string(),
                        val: box inner,
                    }
                }
            },
            TupleAccess { size, ix } => {
                let varpats = ('a'..).map(|c| VarP(c.to_string())).take(*size).collect();
                let mut varexps: Vec<_> = ('a'..).map(|c| Var(c.to_string())).take(*size).collect();
                varexps[*ix] = inner;

                inner = Let {
                    pattern: TupleP(varpats),
                    arg: box rhs_to_why_exp(&stump),
                    body: box Tuple(varexps),
                }
            }
            Down { .. } => {}
        }
        // Remove the last element from the projection
        stump.proj.pop();
    }
}

// [(P as Some)]   ---> [_1]
// [(P as Some).0] ---> let Some(a) = [_1] in a
// [(* P)] ---> * [P]
pub fn rhs_to_why_exp(rhs: &MirPlace) -> MlCfgExp {
    let mut inner = Local(rhs.local);

    for proj in rhs.proj.iter() {
        match proj {
            MutDeref => {
                inner = Current(box inner);
            }
            FieldAccess {
                ctor,
                ix,
                size,
                field,
                kind,
            } => {
                match kind {
                    // Tuple
                    CtorKind::Fn => {
                        let mut pat = vec![Wildcard; *ix];
                        pat.push(VarP("a".into()));
                        pat.append(&mut vec![Wildcard; size - ix - 1]);

                        inner = Let {
                            pattern: ConsP(ctor.to_string(), pat),
                            arg: box inner,
                            body: box Var("a".into()),
                        }
                    }
                    // Unit
                    CtorKind::Const => {
                        assert!(*size == 1 && *ix == 0);
                        unimplemented!();
                    }
                    // Struct
                    CtorKind::Fictive => {
                        inner = Let {
                            pattern: RecP(field.name.to_string(), "a".into()),
                            arg: box inner,
                            body: box Var("a".into()),
                        }
                    }
                }
            }
            TupleAccess { size, ix } => {
                let mut pat = vec![Wildcard; *ix];
                pat.push(VarP("a".into()));
                pat.append(&mut vec![Wildcard; size - ix - 1]);

                inner = Let {
                    pattern: TupleP(pat),
                    arg: box inner,
                    body: box Var("a".into()),
                }
            }
            Down { .. } => {}
        }
    }
    return inner;
}
