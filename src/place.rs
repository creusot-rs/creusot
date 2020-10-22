use rustc_hir::def::CtorKind;
use rustc_middle::{mir::{Body, ProjectionElem::*, Local, Place}, ty::TyCtxt};
use rustc_span::{symbol::Ident, Symbol};

#[derive(Clone, Debug)]
pub enum Projection {
    MutDeref,
    FieldAccess { ctor: Symbol, ix: usize, size: usize, field: Ident, kind: CtorKind },
    TupleAccess { size: usize, ix: usize },
    Down { ctor: Symbol },
}
use Projection::*;

#[derive(Clone, Debug)]
pub struct MirPlace {
    pub local: Local,
    pub proj: Vec<Projection>,
}

pub fn from_place<'tcx>(tcx: TyCtxt<'tcx>, decls: &Body<'tcx>, place: &Place<'tcx>) -> MirPlace {
    let mut place_ty = Place::ty_from(place.local, &[], decls, tcx);

    // TODO: Use a more appropriate type than Vec<ProjElem>
    let mut res_proj = Vec::new();
    for proj in place.projection.iter() {
        match proj {
            Deref => {
                match place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl {
                    rustc_hir::Mutability::Mut => {
                        res_proj.push(MutDeref);
                    }
                    rustc_hir::Mutability::Not => {
                        // Since in the translation [&T] ::= [T], we drop any projections for immutable deref
                    }
                }
            }
            Field(ix, _) => match place_ty.ty.kind() {
                rustc_middle::ty::TyKind::Adt(def, _) => {
                    use rustc_target::abi::VariantIdx;
                    let variant = &def.variants[place_ty.variant_index.unwrap_or(VariantIdx::from_usize(0))];
                    let field = variant.fields[ix.as_usize()].ident;

                    res_proj.push(FieldAccess {
                        ctor: variant.ident.name,
                        ix: ix.as_usize(),
                        size: variant.fields.len(),
                        field,
                        kind: variant.ctor_kind,
                    });
                }
                rustc_middle::ty::TyKind::Tuple(fields) => {
                    res_proj.push(TupleAccess { size: fields.len(), ix: ix.as_usize() })
                }
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

    return MirPlace { local: place.local, proj: res_proj };
}
