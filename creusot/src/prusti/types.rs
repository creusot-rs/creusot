use crate::error::CreusotResult;

use super::{parsing::Home, region_set::*, util::RegionReplacer};
use crate::prusti::{ctx::*, typeck::normalize, with_static::PrettyRegionReplacer};
use itertools::Either;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Mutability,
    ty,
    ty::{AdtDef, List, Region, TyCtxt, TyKind, TypeFoldable},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::VariantIdx;
use std::{
    fmt::{Debug, Display, Formatter},
    iter,
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
    pub(super) home: Region<'tcx>,
}

impl<'tcx> Display for Ty<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.ty, self.home)
    }
}

impl<'tcx> Ty<'tcx> {
    pub(crate) fn as_adt_variant<'a>(
        self,
        variant: VariantIdx,
        ctx: CtxRef<'a, 'tcx>,
    ) -> impl Iterator<Item = Ty<'tcx>> + 'a {
        match self.as_ref(ctx.tcx.lifetimes.re_erased.into()) {
            None => Either::Left(self.as_adt_variant_h(variant, ctx)),
            Some((lft, ty, Mutability::Not)) => Either::Right(
                ty.as_adt_variant_h(variant, ctx)
                    .map(move |ty| Ty { ty: ctx.tcx.mk_imm_ref(lft, ty.ty), home: self.home }),
            ),
            _ => unreachable!(),
        }
    }

    fn as_adt_variant_h<'a>(
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
        tys.zip(iter::repeat(self.home)).map(|(ty, home)| Ty { ty, home })
    }

    pub(super) fn as_ref(self, ts: Region<'tcx>) -> Option<(Region<'tcx>, Self, Mutability)> {
        match self.ty.kind() {
            &TyKind::Ref(region, ty, m) => Some((region, Ty { ty, home: ts }, m)),
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
        Ty { ty: tcx.mk_imm_ref(ts, ty.ty), home: ty.home }
    }

    pub(super) fn try_unbox(self) -> Option<Self> {
        match self.ty.kind() {
            &TyKind::Adt(adt, subst) if adt.is_box() => {
                Some(Ty { ty: subst.types().next().unwrap(), home: self.home })
            }
            _ => None,
        }
    }

    pub(crate) fn never(tcx: TyCtxt<'tcx>) -> Self {
        Ty { ty: tcx.types.never, home: RegionSet::EMPTY.into_region(tcx) }
    }

    pub(crate) fn all_at_ts(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>, ts: Region<'tcx>) -> Self {
        Ty { ty: ty.fold_with(&mut RegionReplacer { tcx, f: |_| ts }), home: ts }
    }

    pub(crate) fn absurd_regions(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self::all_at_ts(ty, tcx, RegionSet::EMPTY.into_region(tcx))
    }

    pub(crate) fn with_absurd_home(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Ty { ty, home: RegionSet::EMPTY.into_region(tcx) }
    }

    pub(crate) fn is_never(self) -> bool {
        self.ty.is_never()
    }

    pub(super) fn has_home_at_ts(self, ts: Region<'tcx>) -> bool {
        sub_ts(self.home, ts)
    }

    pub(super) fn try_new(
        ty: ty::Ty<'tcx>,
        home: Home<Region<'tcx>>,
        _span: Span,
    ) -> CreusotResult<Self> {
        Ok(Ty { ty, home: home.data })
    }
}

pub(super) fn make_region_for_display<'tcx>(
    r: Region<'tcx>,
    ctx: CtxRef<'_, 'tcx>,
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

pub(crate) struct DisplayFoldable<'a, 'tcx, T>(T, pub CtxRef<'a, 'tcx>);

impl<'a, 'tcx, T: Copy + TypeFoldable<TyCtxt<'tcx>> + Display> Display
    for DisplayFoldable<'a, 'tcx, T>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let ctx = self.1.interned;
        let res = self.0.fold_with(&mut PrettyRegionReplacer {
            f: |r| make_region_for_display(r, self.1),
            ctx,
        });
        Display::fmt(&res, f)
    }
}

pub(crate) fn prepare_display<'a, 'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    t: T,
    ctx: CtxRef<'a, 'tcx>,
) -> DisplayFoldable<'a, 'tcx, T> {
    DisplayFoldable(t, ctx)
}
