use super::{region_set::*, util::RegionReplacer};
use crate::prusti::{ctx::*, typeck::normalize, with_static::PrettyRegionReplacer};
use itertools::Either;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Mutability,
    ty,
    ty::{AdtDef, List, Region, TyCtxt, TyKind, TypeFoldable},
};
use rustc_span::Symbol;
use rustc_target::abi::VariantIdx;
use std::{
    fmt::{Debug, Display, Formatter},
};

pub(super) fn sub_ts<'tcx>(ts1: Region<'tcx>, ts2: Region<'tcx>) -> bool {
    RegionSet::from(ts1).subset(RegionSet::from(ts2))
}

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
    pub(crate) fn as_adt_variant<'a>(
        self,
        variant: VariantIdx,
        ctx: CtxRef<'a, 'tcx>,
    ) -> impl Iterator<Item = Ty<'tcx>> + 'a {
        match self.as_ref(ctx.tcx.lifetimes.re_erased.into()) {
            None => Either::Left(self.as_adt_variant_h1(variant, ctx)),
            Some((lft, ty, Mutability::Not)) => Either::Right(
                ty.as_adt_variant_h1(variant, ctx)
                    .map(move |ty| Ty { ty: ctx.tcx.mk_imm_ref(lft, ty.ty) }),
            ),
            _ => unreachable!(),
        }
    }

    fn as_adt_variant_h1<'a>(
        self,
        variant: VariantIdx,
        ctx: CtxRef<'a, 'tcx>,
    ) -> impl Iterator<Item = Ty<'tcx>> + 'a {
        match ctx.zombie_info.as_zombie(self.ty) {
            None => Either::Left(self.as_adt_variant_h2(variant, ctx)),
            Some(ty) => {
                Either::Right(Ty { ty }.as_adt_variant_h2(variant, ctx).map(|ty| Ty {
                    ty: ctx.zombie_info.mk_zombie(ty.ty, ctx.tcx, ctx.param_env()).0,
                }))
            }
        }
    }

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
                    field_defs.iter().map(move |def| normalize(ctx, def.ty(ctx.tcx, *subst_ref))),
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

    pub(super) fn as_ref(self, _: Region<'tcx>) -> Option<(Region<'tcx>, Self, Mutability)> {
        match self.ty.kind() {
            &TyKind::Ref(region, ty, m) => Some((region, Ty { ty }, m)),
            _ => None,
        }
    }

    pub(crate) fn ref_lft(self) -> Region<'tcx> {
        match self.ty.kind() {
            &TyKind::Ref(region, _, _) => region,
            _ => unreachable!(),
        }
    }

    pub(super) fn make_ref(ts: Region<'tcx>, ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Ty { ty: tcx.mk_imm_ref(ts, ty.ty) }
    }

    pub(super) fn try_unbox(self) -> Option<Self> {
        match self.ty.kind() {
            &TyKind::Adt(adt, subst) if adt.is_box() => {
                Some(Ty { ty: subst.types().next().unwrap() })
            }
            _ => None,
        }
    }

    pub(crate) fn all_at_ts(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>, ts: Region<'tcx>) -> Self {
        Ty { ty: ty.fold_with(&mut RegionReplacer { tcx, f: |_| ts }) }
    }

    pub(crate) fn absurd_regions(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self::all_at_ts(ty, tcx, RegionSet::EMPTY.into_region(tcx))
    }

    pub(crate) fn with_absurd_home(ty: ty::Ty<'tcx>, _tcx: TyCtxt<'tcx>) -> Self {
        Ty { ty }
    }

    pub(crate) fn is_never(self) -> bool {
        self.ty.is_never()
    }
}

pub(super) fn make_region_for_display<'tcx>(
    r: Region<'tcx>,
    ctx: &'_  BaseCtx<'_, 'tcx>,
) -> Region<'tcx> {
    let tcx = ctx.tcx;
    let reg_set = RegionSet::from(r);
    if reg_set == RegionSet::UNIVERSE {
        return dummy_region(tcx, Symbol::intern("'?"));
    }
    let mut reg_set_h = reg_set;
    match (reg_set_h.next(), reg_set_h.next()) {
        (None, _) => dummy_region(tcx, Symbol::intern("'!")),
        (Some(x), None) => ctx.base_regions().nth(x as usize).unwrap(),
        _ => {
            use std::fmt::Write;
            let mut f = String::new();
            write!(f, "{{").unwrap();
            let mut iter = reg_set.map(|x| ctx.region_index_to_name(x));
            write!(f, "{}", iter.next().unwrap()).unwrap();
            for x in iter {
                write!(f, "|{x}").unwrap();
            }
            write!(f, "}}").unwrap();
            dummy_region(tcx, Symbol::intern(&*f))
        }
    }
}

pub(crate) struct DisplayFoldable<'a, 'tcx, T>(T, pub &'a BaseCtx<'a, 'tcx>);

/// converts `t` into a form suitable for displaying
pub(crate) fn display_fold<'a, 'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    t: T,
    ctx: &'a BaseCtx<'a, 'tcx>,
) -> T {
    t.fold_with(&mut PrettyRegionReplacer {
        f: |r| make_region_for_display(r, ctx),
        ctx: ctx.interned,
    })
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
