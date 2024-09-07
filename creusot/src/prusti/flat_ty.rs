use crate::prusti::{
    bitvec, bitvec::BitVec, ctx::CtxRef, region_set::StateSet, types::Ty, zombie::ZombieStatus,
};
use rustc_middle::{
    ty,
    ty::{
        Region, TyCtxt, TypeFoldable, TypeFolder, TypeSuperFoldable, TypeSuperVisitable,
        TypeVisitable, TypeVisitor,
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

/// Represents the flattened state sets and zombie statuses from a type
/// Useful for comparing and combining multiple types that are the same modulo states and zombies
#[derive(Debug)]
pub(super) struct FlatTy {
    states: SmallVec<[StateSet; 8]>,
    zombies: BitVec,
}

struct StateZombieVisitor<'a, 'tcx, Z, FS, FZ> {
    ctx: CtxRef<'a, 'tcx>,
    fs: &'a mut FS,
    fz: &'a mut FZ,
    in_zombie: Z,
}

pub(super) fn result_to_cf<T, E>(r: Result<T, E>) -> ControlFlow<E, T> {
    match r {
        Ok(x) => Continue(x),
        Err(e) => Break(e),
    }
}

pub(super) fn cf_to_result<T, E>(r: ControlFlow<E, T>) -> Result<T, E> {
    match r {
        Continue(x) => Ok(x),
        Break(e) => Err(e),
    }
}

impl<'a, 'tcx, Z: Copy, E, FS, FZ> TypeVisitor<TyCtxt<'tcx>>
    for StateZombieVisitor<'a, 'tcx, Z, FS, FZ>
where
    FS: FnMut(StateSet) -> Result<(), E>,
    FZ: FnMut(Z, ZombieStatus) -> Result<Z, E>,
{
    type Result = ControlFlow<E>;
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) -> Self::Result {
        let (status, ty) = Ty { ty }.unpack(self.ctx);
        let in_zombie = result_to_cf((self.fz)(self.in_zombie, status))?;
        let mut visit =
            StateZombieVisitor { ctx: self.ctx, fs: &mut *self.fs, fz: &mut *self.fz, in_zombie };
        ty.super_visit_with(&mut visit)
    }

    fn visit_region(&mut self, r: Region<'tcx>) -> Self::Result {
        result_to_cf((self.fs)(r.into()))
    }
}

fn state_zombie_visit<'tcx, Z: Copy, E, FS, FZ>(
    ctx: CtxRef<'_, 'tcx>,
    ty: Ty<'tcx>,
    mut fs: FS,
    mut fz: FZ,
    in_zombie: Z,
) -> Result<(), E>
where
    FS: FnMut(StateSet) -> Result<(), E>,
    FZ: FnMut(Z, ZombieStatus) -> Result<Z, E>,
{
    cf_to_result(ty.ty.visit_with(&mut StateZombieVisitor {
        ctx,
        fs: &mut fs,
        fz: &mut fz,
        in_zombie,
    }))?;
    Ok(())
}

impl ZombieStatus {
    fn into_bit(self) -> bool {
        match self {
            ZombieStatus::Zombie => true,
            ZombieStatus::NonZombie => false,
        }
    }

    fn from_bit(b: bool) -> Self {
        match b {
            true => ZombieStatus::Zombie,
            false => ZombieStatus::NonZombie,
        }
    }
}

pub(super) fn into_ok<T>(r: Result<T, Infallible>) -> T {
    match r {
        Ok(v) => v,
        Err(e) => match e {},
    }
}

pub(super) fn flatten_ty<'tcx>(ctx: CtxRef<'_, 'tcx>, ty: Ty<'tcx>) -> FlatTy {
    let mut states = SmallVec::new();
    let mut zombies = BitVec::default();
    into_ok(state_zombie_visit(
        ctx,
        ty,
        |ss| Ok(states.push(ss)),
        |(), zs| Ok(zombies.push(zs.into_bit())),
        (),
    ));
    FlatTy { states, zombies }
}

fn walk_with_flat_ty<'tcx, FS, FZ, E>(
    ctx: CtxRef<'_, 'tcx>,
    flat: &mut FlatTy,
    ty: Ty<'tcx>,
    fs: FS,
    fz: FZ,
) -> Result<(), E>
where
    FS: Fn(StateSet, StateSet) -> Result<StateSet, E>,
    FZ: Fn(bool, ZombieStatus, ZombieStatus) -> Result<ZombieStatus, E>,
{
    let FlatTy { states, zombies } = flat;
    let mut state_count = 0;
    let mut zombie_count = 0;
    state_zombie_visit(
        ctx,
        ty,
        |state| {
            states[state_count] = fs(states[state_count], state)?;
            state_count += 1;
            Ok(())
        },
        |in_zombie, status| {
            let status1 = ZombieStatus::from_bit(zombies.get(zombie_count));
            zombies.set(zombie_count, fz(in_zombie, status1, status)?.into_bit());
            zombie_count += 1;
            let in_zombie = !matches!(
                (in_zombie, status1, status),
                (false, ZombieStatus::NonZombie, ZombieStatus::NonZombie)
            );
            Ok(in_zombie)
        },
        false,
    )
}

pub(super) fn union<'tcx>(ctx: CtxRef<'_, 'tcx>, flat: &mut FlatTy, ty: Ty<'tcx>) {
    into_ok(walk_with_flat_ty(
        ctx,
        flat,
        ty,
        |s1, s2| Ok(s1.union(s2)),
        |in_zombie, s1, s2| {
            Ok(match (in_zombie, s1, s2) {
                (true, _, _) => ZombieStatus::NonZombie,
                (false, ZombieStatus::NonZombie, ZombieStatus::NonZombie) => {
                    ZombieStatus::NonZombie
                }
                (false, _, _) => ZombieStatus::Zombie,
            })
        },
    ))
}

#[derive(Debug)]
pub(super) enum CheckSupError {
    ZombieMismatch,
    StateMismatch { expected: StateSet, found: StateSet },
}

pub(super) fn check_sup<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    mut expected: FlatTy,
    actual: Ty<'tcx>,
) -> Result<(), CheckSupError> {
    walk_with_flat_ty(
        ctx,
        &mut expected,
        actual,
        |expected, found| {
            if found.subset(expected) {
                Ok(expected)
            } else {
                Err(CheckSupError::StateMismatch { expected, found })
            }
        },
        |in_zombie, expected, actual| match (in_zombie, expected, actual) {
            (false, ZombieStatus::NonZombie, ZombieStatus::Zombie) => {
                Err(CheckSupError::ZombieMismatch)
            }
            _ => Ok(expected),
        },
    )
}

struct FlatTyBuilder<'a, 'tcx> {
    ctx: CtxRef<'a, 'tcx>,
    states: slice::Iter<'a, StateSet>,
    zombies: bitvec::Iter<'a>,
}

impl<'a, 'tcx> TypeFolder<TyCtxt<'tcx>> for FlatTyBuilder<'a, 'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }

    fn fold_ty(&mut self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        let (_, ty) = Ty { ty }.unpack(self.ctx);
        let status = ZombieStatus::from_bit(self.zombies.next().unwrap());
        let ty = ty.super_fold_with(self);
        Ty { ty }.pack(status, self.ctx).ty
    }

    fn fold_region(&mut self, _: Region<'tcx>) -> Region<'tcx> {
        self.ctx.mk_region(*self.states.next().unwrap())
    }
}

pub(super) fn flat_to_ty<'tcx>(
    ctx: CtxRef<'_, 'tcx>,
    flat_ty: &FlatTy,
    skeleton: Ty<'tcx>,
) -> Ty<'tcx> {
    let mut b =
        FlatTyBuilder { ctx, states: flat_ty.states.iter(), zombies: flat_ty.zombies.iter() };
    Ty { ty: skeleton.ty.fold_with(&mut b) }
}
