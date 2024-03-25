use crate::prusti::{
    ctx::CtxRef,
    flat_ty::{cf_to_result, into_ok, result_to_cf, CheckSupError},
    region_set::StateSet,
    types::Ty,
    zombie::ZombieStatus,
};
use rustc_middle::{
    bug, ty,
    ty::{
        InferTy, Region, RegionKind, RegionVid, TyCtxt, TyKind, TypeSuperVisitable, TypeVisitable,
        TypeVisitor,
    },
};
use smallvec::SmallVec;
use std::{
    convert::Infallible,
    ops::{
        ControlFlow,
        ControlFlow::{Break, Continue},
    },
    slice,
};

type RegT = u16;
type TyT = u16;
type DistT = u16;

#[derive(Copy, Clone)]
pub(super) enum RustReg {
    Static,
    Var(RegionVid),
}

impl RustReg {
    fn compress(self) -> RegT {
        match self {
            RustReg::Static => RegT::MAX,
            RustReg::Var(vid) => {
                let x: u32 = vid.as_u32();
                assert!(x < RegT::MAX.into());
                x.try_into().unwrap()
            }
        }
    }

    fn from_compressed(compressed: RegT) -> Self {
        if compressed == RegT::MAX {
            RustReg::Static
        } else {
            RustReg::Var(RegionVid::from_u32(compressed.into()))
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct TyVarDist {
    dist: DistT,
    var: TyT,
}

/// Represents the flattened region and type variables a rust type
/// Useful for comparing and combining multiple types that are the same modulo states and zombies
#[derive(Debug)]
pub(super) struct RustFlatTy {
    reg_vars: SmallVec<[RegT; 8]>,
    ty_vars: SmallVec<[TyVarDist; 4]>,
}

struct RustTyFlatBuilder {
    dist: DistT,
    flat: RustFlatTy,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for RustTyFlatBuilder {
    type BreakTy = Infallible;
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        match ty.kind() {
            TyKind::Infer(InferTy::FreshTy(var)) => {
                let var = (*var).try_into().unwrap();
                let dist = self.dist;
                self.dist = 0;
                self.flat.ty_vars.push(TyVarDist { var, dist });
                Continue(())
            }
            _ => {
                self.dist += 1;
                ty.super_visit_with(self)
            }
        }
    }

    fn visit_region(&mut self, r: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        let r = match r.kind() {
            RegionKind::ReVar(vid) => RustReg::Var(vid),
            RegionKind::ReStatic => RustReg::Static,
            _ => bug!(),
        };
        self.flat.reg_vars.push(r.compress());
        Continue(())
    }
}

pub(super) fn flatten_rust_ty<'tcx>(ty: ty::Ty<'tcx>) -> RustFlatTy {
    let flat = RustFlatTy { reg_vars: SmallVec::new(), ty_vars: SmallVec::new() };
    let mut v = RustTyFlatBuilder { dist: 0, flat };
    into_ok(cf_to_result(ty.visit_with(&mut v)));
    v.flat
}

struct WithRustTyFlatVisitor<'a, 'tcx, FS, FT> {
    ctx: CtxRef<'a, 'tcx>,
    next: Option<TyVarDist>,
    ty_vars: slice::Iter<'a, TyVarDist>,
    reg_vars: slice::Iter<'a, RegT>,
    fs: FS,
    ft: FT,
}

impl<'a, 'tcx, FS, FT> TypeVisitor<TyCtxt<'tcx>> for WithRustTyFlatVisitor<'a, 'tcx, FS, FT>
where
    FS: FnMut(StateSet, RustReg) -> Result<(), CheckSupError>,
    FT: FnMut(Ty<'tcx>, u32) -> Result<(), CheckSupError>,
{
    type BreakTy = CheckSupError;
    fn visit_region(&mut self, r: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        result_to_cf((self.fs)(r.into(), RustReg::from_compressed(*self.reg_vars.next().unwrap())))
    }

    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        let ty = Ty { ty };
        match &mut self.next {
            Some(TyVarDist { var, dist }) => {
                if *dist == 0 {
                    let res = (self.ft)(ty, (*var).into());
                    self.next = self.ty_vars.next().copied();
                    return result_to_cf(res);
                } else {
                    *dist -= 1;
                }
            }
            None => {}
        }
        let (status, ty) = ty.unpack(self.ctx);
        if let ZombieStatus::Zombie = status {
            return Break(CheckSupError::ZombieMismatch);
        }
        ty.super_visit_with(self)
    }
}

pub(super) fn walk_with_rust_flat_ty<'tcx, FS, FT>(
    ctx: CtxRef<'_, 'tcx>,
    flat: &RustFlatTy,
    ty: Ty<'tcx>,
    fs: FS,
    ft: FT,
) -> Result<(), CheckSupError>
where
    FS: FnMut(StateSet, RustReg) -> Result<(), CheckSupError>,
    FT: FnMut(Ty<'tcx>, u32) -> Result<(), CheckSupError>,
{
    let mut ty_vars = flat.ty_vars.iter();
    let reg_vars = flat.reg_vars.iter();
    let next = ty_vars.next().copied();
    let mut v = WithRustTyFlatVisitor { ctx, next, ty_vars, reg_vars, fs, ft };
    cf_to_result(ty.ty.visit_with(&mut v))
}
