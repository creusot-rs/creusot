use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Local, Place, *},
    ty::TyCtxt,
};
use rustc_target::abi::VariantIdx;

// This representation is not strictly needed, but I find that it still splits up the
// work between the translation to MLCfg and MIR nicely.
pub use rustc_hir::Mutability;

#[derive(Clone, Debug)]
pub enum Projection {
    Deref(Mutability),
    FieldAccess { base_ty: DefId, ctor: VariantIdx, ix: usize },
    TupleAccess { size: usize, ix: usize },
    // Down { ctor: Symbol },
}
use Projection::*;

#[derive(Clone, Debug)]
pub struct SimplePlace {
    pub local: Local,
    pub proj: Vec<Projection>,
}

pub fn simplify_place<'tcx>(tcx: TyCtxt<'tcx>, decls: &Body<'tcx>, place: &Place<'tcx>) -> SimplePlace {
    let mut place_ty = Place::ty_from(place.local, &[], decls, tcx);

    let mut res_proj = Vec::new();
    for proj in place.projection.iter() {
        match proj {
            ProjectionElem::Deref => {
                let mutability = place_ty.ty.builtin_deref(false).expect("raw pointer").mutbl;
                res_proj.push(Deref(mutability));
            }
            ProjectionElem::Field(ix, _) => match place_ty.ty.kind() {
                rustc_middle::ty::TyKind::Adt(def, _) => {
                    let variant_id = place_ty.variant_index.unwrap_or_else(|| 0u32.into());

                    res_proj.push(FieldAccess { base_ty: def.did, ctor: variant_id, ix: ix.as_usize() });
                }
                rustc_middle::ty::TyKind::Tuple(fields) => {
                    res_proj.push(TupleAccess { size: fields.len(), ix: ix.as_usize() })
                }
                _ => {
                    panic!("accessing field on unexpected tykind");
                }
            },
            ProjectionElem::Downcast(_, _) => {}
            _ => {
                panic!("unsupported place projection");
            }
        }
        place_ty = place_ty.projection_ty(tcx, proj);
    }

    SimplePlace { local: place.local, proj: res_proj }
}
