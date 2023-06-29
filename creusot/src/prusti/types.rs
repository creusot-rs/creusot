use crate::error::{CreusotResult, Error};

use super::{parsing::Home, region_set::*, util::RegionReplacer};
use itertools::Either;
use rustc_infer::infer::region_constraints::Constraint;
use rustc_lint::Lint;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Mutability,
    ty,
    ty::{AdtDef, BoundRegionKind, List, ParamEnv, Region, TyCtxt, TyKind, TypeFoldable},
};
use rustc_span::{
    def_id::{DefId, LocalDefId, CRATE_DEF_ID},
    Span, Symbol,
};
use rustc_target::abi::VariantIdx;
use std::{
    fmt::{Debug, Display, Formatter},
    iter,
};
use crate::prusti::typeck::normalize;

const CURR_STR: &str = "'curr";
const OLD_STR: &str = "'old";

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
        ctx: &'a Ctx<'tcx>,
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
        ctx: &'a Ctx<'tcx>,
    ) -> impl Iterator<Item = Ty<'tcx>> + 'a {
        let tys = match self.ty.kind() {
            TyKind::Adt(adt, subst_ref) => {
                let adt: AdtDef = *adt;
                let field_defs = &adt.variants()[variant].fields;
                Either::Left(field_defs.iter().map(move |def| normalize(ctx, def.ty(ctx.tcx, *subst_ref))))
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

pub(super) fn sub_ts<'tcx>(ts1: Region<'tcx>, ts2: Region<'tcx>) -> bool {
    RegionSet::from(ts1).subset(RegionSet::from(ts2))
}

const OLD_IDX: u8 = 0;
const CURR_IDX: u8 = 1;
const OLD_REG_SET: RegionSet = RegionSet::singleton(OLD_IDX as u32);
const CURR_REG_SET: RegionSet = RegionSet::singleton(CURR_IDX as u32);

pub(crate) struct Ctx<'tcx, R = RegionRelation> {
    pub tcx: TyCtxt<'tcx>,
    base_regions: Vec<Region<'tcx>>,
    pub(super) relation: R,
    pub curr_sym: Symbol,
    pub owner_id: LocalDefId,
    is_logic: bool,
}

/// Primarily intended for logic functions with home signatures where since the homes might not be bound
/// allows adding to base_regions on the fly and waits to build the relation until then end
pub(crate) type PreCtx<'tcx> = Ctx<'tcx, ()>;

impl<'tcx, X: Debug> Debug for Ctx<'tcx, X> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let name = if std::mem::size_of::<X>() == 0 { "PreCtx" } else { "Ctx" };
        f.debug_struct(name)
            .field("base_regions", &self.base_regions)
            .field("relation", &self.relation)
            .field("owner_id", &self.owner_id)
            .finish_non_exhaustive()
    }
}

fn dummy_region(tcx: TyCtxt<'_>, sym: Symbol) -> Region<'_> {
    let def_id = CRATE_DEF_ID.to_def_id();
    tcx.mk_re_free(def_id, BoundRegionKind::BrNamed(def_id, sym))
}

fn try_index_of<T: Eq>(s: &[T], x: &T) -> Option<usize> {
    Some(s.iter().enumerate().find(|&(_, y)| x == y)?.0)
}

fn index_of<T: Eq + Debug>(s: &[T], x: &T) -> usize {
    try_index_of(s, x).expect(&format!("{s:?} did not contain {x:?}"))
}

fn ty_regions<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Vec<Region<'tcx>> {
    let mut v = Vec::new();
    ty.fold_with(&mut RegionReplacer {
        tcx,
        f: |r| {
            v.push(r);
            r
        },
    });
    v
}

impl<'tcx, X> Ctx<'tcx, X> {
    pub(crate) fn base_regions(&self) -> impl Iterator<Item = Region<'tcx>> + '_ {
        self.base_regions.iter().copied()
    }

    pub(crate) fn old_region(&self) -> Region<'tcx> {
        OLD_REG_SET.into_region(self.tcx)
    }

    pub(crate) fn curr_region(&self) -> Region<'tcx> {
        CURR_REG_SET.into_region(self.tcx)
    }

    pub(super) fn param_env(&self) -> ParamEnv<'tcx> {
        // We want to ignore outlives constraints
        let base: ParamEnv = self.tcx.param_env(self.owner_id);
        self.tcx.erase_regions(base)
    }

    pub(crate) fn lint(&self, lint: &'static Lint, span: Span, msg: String) {
        let hir_id = self.tcx.local_def_id_to_hir_id(self.owner_id);
        self.tcx.struct_span_lint_hir(lint, hir_id, span, msg, |x| x)
    }

    fn try_home_to_region(&self, s: Symbol) -> Option<Region<'tcx>> {
        if s == self.curr_sym {
            return Some(self.curr_region());
        }
        for (idx, reg) in self.base_regions.iter().enumerate() {
            if Some(s) == reg.get_name() {
                return Some(RegionSet::singleton(idx as u32).into_region(self.tcx));
            }
        }
        None
    }

    fn user_region_to_region(&self, r: Region<'tcx>) -> Option<Region<'tcx>> {
        self.try_home_to_region(r.get_name()?)
    }

    pub(crate) fn fix_user_ty_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&self, t: T) -> T {
        let t = normalize(self, t);
        let tcx = self.tcx;
        t.fold_with(&mut RegionReplacer {
            tcx,
            f: |r| self.user_region_to_region(r).unwrap_or(tcx.lifetimes.re_erased),
        })
    }
}

impl<'tcx> PreCtx<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, owner_id: DefId) -> Self {
        let curr_sym = Symbol::intern(CURR_STR);
        let curr_region = dummy_region(tcx, curr_sym);
        let old_region = dummy_region(tcx, Symbol::intern(OLD_STR));
        let base_regions = vec![old_region, curr_region];
        Ctx {
            tcx,
            relation: (),
            base_regions,
            curr_sym,
            owner_id: owner_id.expect_local(),
            is_logic: true,
        }
    }

    pub(super) fn home_to_region(&mut self, s: Symbol) -> Region<'tcx> {
        if let Some(x) = self.try_home_to_region(s) {
            return x;
        }
        let idx = self.base_regions.len();
        self.base_regions.push(dummy_region(self.tcx, s));
        // homes that are not declared
        RegionSet::singleton(idx as u32).into_region(self.tcx)
    }

    pub(super) fn map_parsed_home(&mut self, home: Home) -> Home<Region<'tcx>> {
        Home { data: self.home_to_region(home.data) }
    }

    /// Fixes an external region by converting it into a singleton set
    pub(super) fn fix_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        if r.get_name() == Some(self.curr_sym) {
            return self.curr_region();
        }
        let idx = match try_index_of(&self.base_regions, &r) {
            Some(idx) => idx,
            None => {
                let idx = self.base_regions.len();
                self.base_regions.push(r);
                idx
            }
        };
        RegionSet::singleton(idx as u32).into_region(self.tcx)
    }

    pub(super) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&mut self, t: T) -> T {
        let t = normalize(self, t);
        let tcx = self.tcx;
        t.fold_with(&mut RegionReplacer { tcx, f: |r| self.fix_region(r) })
    }

    pub(super) fn finish_for_logic(self, iter: impl Iterator<Item = Ty<'tcx>>) -> Ctx<'tcx> {
        let reg_to_idx = |r: Region| RegionSet::from(r).next().unwrap() as usize;
        let iter = iter
            .flat_map(|x| {
                ty_regions(x.ty, self.tcx)
                    .into_iter()
                    .map(move |r| (reg_to_idx(r), reg_to_idx(x.home)))
            })
            .filter(|(r1, r2)| *r1 == usize::from(CURR_IDX) || *r2 == usize::from(CURR_IDX));
        let relation = RegionRelation::new(self.base_regions.len(), iter);
        Ctx { relation, ..self }
    }
}

impl<'tcx> Ctx<'tcx> {
    pub(super) fn new_for_spec(tcx: TyCtxt<'tcx>, owner_id: DefId) -> CreusotResult<Self> {
        let mut res = PreCtx::new(tcx, owner_id);
        let (rs, constraints) = super::variance::constraints_of_fn(tcx, owner_id.expect_local());
        let mut cur_region = None;

        // Add all regions (if any of them are 'curr replace the curr_region instead
        res.base_regions.extend(rs.filter_map(|x| {
            if x.get_name() == Some(res.curr_sym) {
                cur_region = Some(x);
                None
            } else {
                Some(x)
            }
        }));
        if let Some(cur_region) = cur_region {
            res.base_regions[usize::from(CURR_IDX)] = cur_region
        }

        let mut failed = false;
        let reg_to_idx = |r| index_of(&res.base_regions, &r);
        let mut assert_not_curr = |r: Region<'tcx>| {
            if r.get_name() == Some(res.curr_sym) {
                failed = true;
            };
            r
        };
        let constraints = constraints
            .map(|c| match c {
                Constraint::VarSubReg(_, r1) => {
                    (reg_to_idx(assert_not_curr(r1)), CURR_IDX as usize)
                }
                Constraint::RegSubReg(r2, r1) => (reg_to_idx(assert_not_curr(r1)), reg_to_idx(r2)),
                _ => (CURR_IDX.into(), CURR_IDX.into()),
            })
            .chain(iter::once((CURR_IDX.into(), OLD_IDX.into())));
        let relation = RegionRelation::new(res.base_regions.len(), constraints);
        if failed {
            return Err(Error::new(
                tcx.def_ident_span(owner_id).unwrap(),
                format!("{CURR_STR} region must not be blocked"),
            ));
        }

        Ok(Ctx { relation, is_logic: false, ..res })
    }

    pub(super) fn curr_home(&self) -> Home {
        self.curr_sym.into()
    }

    fn region_index_to_name(&self, idx: u32) -> Symbol {
        self.base_regions[idx as usize].get_name().unwrap_or(Symbol::intern("'_"))
    }

    /// Fixes an external region by converting it into a singleton set
    pub(super) fn fix_region(&self, r: Region<'tcx>) -> Region<'tcx> {
        if r.is_erased() {
            return RegionSet::UNIVERSE.into_region(self.tcx);
        }
        let idx = index_of(&self.base_regions, &r);
        let res = RegionSet::singleton(idx as u32);
        if self.relation.idx_outlived_by(CURR_IDX.into(), res) || self.is_logic {
            res.into_region(self.tcx)
        } else {
            self.curr_region()
        }
    }

    pub(super) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&self, t: T) -> T {
        let t = normalize(self, t);
        let tcx = self.tcx;
        t.fold_with(&mut RegionReplacer { tcx, f: |r| self.fix_region(r) })
    }
}

pub(super) struct DisplayRegion<'a, 'tcx>(pub Region<'tcx>, pub &'a Ctx<'tcx>);

impl<'a, 'tcx> Display for DisplayRegion<'a, 'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let reg_set = RegionSet::from(self.0);
        if reg_set == RegionSet::UNIVERSE {
            return write!(f, "'?");
        }
        // write!(f, "({reg_set:?})")?;
        let mut reg_set_h = reg_set;
        match (reg_set_h.next(), reg_set_h.next()) {
            (None, _) => write!(f, "'!"),
            (Some(x), None) => write!(f, "{}", self.1.region_index_to_name(x)),
            _ => {
                write!(f, "{{")?;
                let mut iter = reg_set.map(|x| self.1.region_index_to_name(x));
                write!(f, "{}", iter.next().unwrap())?;
                for x in iter {
                    write!(f, "|{x}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

pub(super) fn make_region_for_display<'tcx>(r: Region<'tcx>, ctx: &Ctx<'tcx>) -> Region<'tcx> {
    let dr = DisplayRegion(r, ctx);
    let sym = Symbol::intern(&format!("{dr}",));
    dummy_region(ctx.tcx, sym)
}

pub(crate) struct DisplayFoldable<'a, 'tcx, T>(T, pub &'a Ctx<'tcx>);

impl<'a, 'tcx, T: Copy + TypeFoldable<TyCtxt<'tcx>> + Display> Display
    for DisplayFoldable<'a, 'tcx, T>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let tcx = self.1.tcx;
        let res = self
            .0
            .fold_with(&mut RegionReplacer { f: |r| make_region_for_display(r, self.1), tcx });
        Display::fmt(&res, f)
    }
}

pub(crate) fn prepare_display<'a, 'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    t: T,
    ctx: &'a Ctx<'tcx>,
) -> DisplayFoldable<'a, 'tcx, T> {
    DisplayFoldable(t, ctx)
}
