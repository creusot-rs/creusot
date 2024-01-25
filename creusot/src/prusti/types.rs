use super::region_set::*;
use crate::prusti::{
    ctx::*,
    typeck::{mk_zombie, normalize},
    zombie::{pretty_replace, ZombieStatus},
};
use itertools::Either;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Mutability,
    ty,
    ty::{AdtDef, List, Region, TyCtxt, TyKind, TypeFoldable},
};
use rustc_span::Symbol;
use rustc_target::abi::VariantIdx;
use std::fmt::{Debug, Display, Formatter};

#[derive(Copy, Clone, Debug, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable)]
/// Since we use a different subtyping for this analysis
/// All regions are represented as early bound regions
/// The index is used as a bitset of possible source regions that could have flowed into this region
pub(crate) struct Ty<'tcx> {
    pub(crate) ty: ty::Ty<'tcx>,
}

impl<'tcx> Display for Ty<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ty)
    }
}

impl<'tcx> Ty<'tcx> {
    pub(super) fn pack(self, status: ZombieStatus, ctx: CtxRef<'_, 'tcx>) -> Self {
        match status {
            ZombieStatus::NonZombie => self,
            ZombieStatus::Zombie => Ty { ty: ctx.zombie_info.mk_zombie_raw(self.ty, ctx.tcx) },
        }
    }

    pub(crate) fn unpack(self, ctx: CtxRef<'_, 'tcx>) -> (ZombieStatus, ty::Ty<'tcx>) {
        match ctx.zombie_info.as_zombie(self.ty) {
            None => (ZombieStatus::NonZombie, self.ty),
            Some(ty) => (ZombieStatus::Zombie, ty),
        }
    }

    pub(super) fn mk_zombie(self, ctx: CtxRef<'_, 'tcx>) -> (Self, bool) {
        let (ty, z) = mk_zombie(self.ty, ctx);
        (Ty { ty }, z)
    }

    pub fn is_snap_eq(self, ctx: CtxRef<'_, 'tcx>) -> bool {
        ctx.zombie_info.is_snap_eq(self.ty, ctx)
    }

    pub(crate) fn as_adt_variant<'a>(
        self,
        variant: VariantIdx,
        ctx: CtxRef<'a, 'tcx>,
    ) -> impl Iterator<Item = Ty<'tcx>> + 'a {
        match self.as_ref(ctx) {
            None => Either::Left(self.as_adt_variant_h1(variant, ctx)),
            Some((lft, ty, _, Mutability::Not)) => Either::Right(
                ty.as_adt_variant_h1(variant, ctx).map(move |ty| Ty::make_ref(lft, ty, ctx)),
            ),
            _ => unreachable!(),
        }
    }

    fn as_adt_variant_h1<'a>(
        self,
        variant: VariantIdx,
        ctx: CtxRef<'a, 'tcx>,
    ) -> impl Iterator<Item = Ty<'tcx>> + 'a {
        match self.unpack(ctx) {
            (ZombieStatus::NonZombie, ty) => {
                Either::Left(Ty { ty }.as_adt_variant_h2(variant, ctx))
            }
            (ZombieStatus::Zombie, ty) => Either::Right(
                Ty { ty }.as_adt_variant_h2(variant, ctx).map(|ty| ty.mk_zombie(ctx).0),
            ),
        }
    }

    // NOTE self has already been unpacked here
    fn as_adt_variant_h2<'a>(
        self,
        variant: VariantIdx,
        ctx: CtxRef<'a, 'tcx>,
    ) -> impl Iterator<Item = Ty<'tcx>> + 'a {
        let tys = match self.ty.kind() {
            TyKind::Adt(adt, subst_ref) => {
                let adt: AdtDef = *adt;
                let field_defs = &adt.variants()[variant].fields;
                Either::Left(
                    field_defs.iter().map(move |def| normalize(ctx, def.ty(ctx.tcx, subst_ref))),
                )
            }
            TyKind::Tuple(tup) => {
                let tup: &List<ty::Ty> = tup;
                Either::Right(tup.iter())
            }
            _ => unreachable!(),
        };
        tys.map(|ty| Ty { ty })
    }

    pub(super) fn as_ref(
        self,
        ctx: CtxRef<'_, 'tcx>,
    ) -> Option<(Region<'tcx>, Self, ZombieStatus, Mutability)> {
        let (status, ty) = self.unpack(ctx);
        match ty.kind() {
            &TyKind::Ref(region, ty, m) => Some((region, Ty { ty }, status, m)),
            _ => None,
        }
    }

    pub(super) fn make_ref(ts: Region<'tcx>, ty: Ty<'tcx>, ctx: CtxRef<'_, 'tcx>) -> Self {
        Ty { ty: ctx.tcx.mk_imm_ref(ts, ty.ty) }.pack(ZombieStatus::NonZombie, ctx)
    }
}

pub(super) fn make_region_for_display<'tcx>(
    reg_set: StateSet,
    ctx: &'_ BaseCtx<'_, 'tcx>,
) -> Region<'tcx> {
    let tcx = ctx.tcx;
    if reg_set == StateSet::UNIVERSE {
        return dummy_region(tcx, Symbol::intern("'?"));
    }
    let mut reg_set_h = reg_set;
    match (reg_set_h.next(), reg_set_h.next()) {
        (None, _) => dummy_region(tcx, Symbol::intern("'!")),
        (Some(x), None) => ctx.base_states()[x],
        _ => {
            use std::fmt::Write;
            let mut f = String::new();
            write!(f, "{{").unwrap();
            let mut iter = reg_set.map(|x| ctx.state_to_name(x));
            write!(f, "{}", iter.next().unwrap()).unwrap();
            for x in iter {
                write!(f, "|{x}").unwrap();
            }
            write!(f, "}}").unwrap();
            dummy_region(tcx, Symbol::intern(&f))
        }
    }
}

pub(crate) struct DisplayFoldable<'a, 'tcx, T>(T, pub &'a BaseCtx<'a, 'tcx>);

/// converts `t` into a form suitable for displaying
pub(crate) fn display_fold<'a, 'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    t: T,
    ctx: &'a BaseCtx<'a, 'tcx>,
) -> T {
    pretty_replace(ctx.interned, |r| make_region_for_display(r.into(), ctx), t)
}

impl<'a, 'tcx, T: Copy + TypeFoldable<TyCtxt<'tcx>> + Display> Display
    for DisplayFoldable<'a, 'tcx, T>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let res = display_fold(self.0, self.1);
        Display::fmt(&res, f)
    }
}

/// Similar to [`display_fold`] but does the conversion lazily when [`Display::fmt`] is called
pub(crate) fn prepare_display<'a, 'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    t: T,
    ctx: CtxRef<'a, 'tcx>,
) -> DisplayFoldable<'a, 'tcx, T> {
    DisplayFoldable(t, &ctx.base)
}

pub(crate) fn display_state<'tcx>(t: State, ctx: CtxRef<'_, 'tcx>) -> impl Display + 'tcx {
    ctx.base_states()[t]
}
