use crate::error::{CreusotResult, Error};

use super::{parsing::Home, region_set::*};
use crate::prusti::{
    parsing::Outlives,
    typeck::normalize,
    types::{prepare_display, Ty},
    with_static::{FixingRegionReplacer, StaticNormalizerDefIds},
    zombie::ZombieDefIds,
};
use rustc_infer::infer::region_constraints::Constraint;
use rustc_lint::Lint;
use rustc_middle::{
    ty,
    ty::{walk::TypeWalker, BoundRegionKind, ParamEnv, Region, TyCtxt, TypeFoldable},
};
use rustc_span::{
    def_id::{DefId, LocalDefId, CRATE_DEF_ID},
    Span, Symbol,
};
use std::{
    fmt::{Debug, Formatter},
    iter,
    ops::Deref,
};
use rustc_index::{Idx, IndexVec};

const CURR_STR: &str = "'curr";
const OLD_STR: &str = "'old";

const OLD_STATE: State = State(0);
const STATIC_STATE: State = State(1);
const CURR_STATE: State = State(2);
const OLD_REG_SET: StateSet = StateSet::singleton(OLD_STATE);
pub(super) const STATIC_REG_SET: StateSet = StateSet::singleton(STATIC_STATE);
pub(super) const CURR_REG_SET: StateSet = StateSet::singleton(CURR_STATE);

#[derive(Debug)]
enum FnType {
    Logic { valid_states: StateSet },
    Program,
}

pub(crate) struct InternedInfo<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub curr_sym: Symbol,
    pub(super) static_replacer_info: StaticNormalizerDefIds,
    pub zombie_info: ZombieDefIds,
}

pub(crate) struct BaseCtx<'a, 'tcx> {
    pub interned: &'a InternedInfo<'tcx>,
    base_states: IndexVec<State, Region<'tcx>>,
    pub(super) owner_id: LocalDefId,
    param_env: ParamEnv<'tcx>,
    fn_type: FnType,
}

impl<'a, 'tcx> Deref for BaseCtx<'a, 'tcx> {
    type Target = InternedInfo<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.interned
    }
}

#[derive(Debug)]
pub(crate) struct Ctx<'a, 'tcx> {
    pub base: BaseCtx<'a, 'tcx>,
    pub(super) relation: RegionRelation,
}

impl<'a, 'tcx> Deref for Ctx<'a, 'tcx> {
    type Target = BaseCtx<'a, 'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

/// Primarily intended for logic functions with home signatures where since the homes might not be bound
/// allows adding to base_states on the fly and waits to build the relation until then end
#[derive(Debug)]
pub(crate) struct PreCtx<'a, 'tcx> {
    pub base: BaseCtx<'a, 'tcx>,
}

impl<'a, 'tcx> Deref for PreCtx<'a, 'tcx> {
    type Target = BaseCtx<'a, 'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

impl<'a, 'tcx> Debug for BaseCtx<'a, 'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BaseCtx")
            .field("base_states", &self.base_states)
            .field("owner_id", &self.owner_id)
            .field("param_env", &self.param_env)
            .finish_non_exhaustive()
    }
}

pub(super) fn dummy_region(tcx: TyCtxt<'_>, sym: Symbol) -> Region<'_> {
    let def_id = CRATE_DEF_ID.to_def_id();
    Region::new_free(tcx, def_id, BoundRegionKind::BrNamed(def_id, sym))
}

fn try_index_of<I: Idx, T: Eq>(s: &IndexVec<I, T>, x: &T) -> Option<I> {
    Some(s.iter_enumerated().find(|&(_, y)| x == y)?.0)
}

fn index_of<I: Idx, T: Eq + Debug>(s: &IndexVec<I, T>, x: &T) -> I {
    try_index_of(s, x).expect(&format!("{s:?} did not contain {x:?}"))
}

fn ty_regions<'tcx>(ty: ty::Ty<'tcx>) -> impl Iterator<Item = Region<'tcx>> {
    TypeWalker::new(ty.into()).filter_map(|x| x.as_region())
}

impl<'tcx> InternedInfo<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            curr_sym: Symbol::intern(CURR_STR),
            static_replacer_info: StaticNormalizerDefIds::new(tcx),
            zombie_info: ZombieDefIds::new(tcx),
        }
    }

    pub(crate) fn mk_region(&self, rs: StateSet) -> Region<'tcx> {
        rs.into_region(self.tcx)
    }

    pub(crate) fn old_region(&self) -> Region<'tcx> {
        self.mk_region(OLD_REG_SET)
    }

    pub(crate) fn curr_region(&self) -> Region<'tcx> {
        self.mk_region(CURR_REG_SET)
    }

    pub(crate) fn static_region(&self) -> Region<'tcx> {
        self.mk_region(STATIC_REG_SET)
    }
}

impl<'a, 'tcx> BaseCtx<'a, 'tcx> {
    pub(crate) fn base_states(&self) -> &IndexVec<State, Region<'tcx>> {
        &self.base_states
    }

    pub(super) fn param_env(&self) -> ParamEnv<'tcx> {
        // We want to ignore outlives constraints
        self.param_env
    }

    pub(crate) fn lint(&self, lint: &'static Lint, span: Span, msg: impl Into<String>) {
        let hir_id = self.tcx.local_def_id_to_hir_id(self.owner_id);
        self.tcx.struct_span_lint_hir(lint, hir_id, span, msg.into(), |x| x)
    }

    fn try_home_to_region(&self, s: Symbol) -> Option<Region<'tcx>> {
        if s == self.curr_sym {
            return Some(self.curr_region());
        }
        for (idx, reg) in self.base_states.iter_enumerated() {
            if Some(s) == reg.get_name() {
                return Some(StateSet::singleton(idx).into_region(self.tcx));
            }
        }
        None
    }

    fn user_region_to_region(&self, r: Region<'tcx>) -> Option<Region<'tcx>> {
        self.try_home_to_region(r.get_name()?)
    }

    fn new(interned: &'a InternedInfo<'tcx>, owner_id: DefId) -> Self {
        let tcx = interned.tcx;
        let curr_region = dummy_region(tcx, interned.curr_sym);
        let old_region = dummy_region(tcx, Symbol::intern(OLD_STR));
        let base_states = [old_region, tcx.lifetimes.re_static, curr_region].into_iter().collect();
        let base: ParamEnv = tcx.param_env(owner_id);
        let fixed = base.fold_with(&mut FixingRegionReplacer { ctx: interned, f: |r| r });
        let erased = tcx.erase_regions(fixed);
        BaseCtx {
            interned,
            base_states,
            owner_id: owner_id.expect_local(),
            fn_type: FnType::Logic { valid_states: StateSet::EMPTY },
            param_env: erased,
        }
    }

    pub(crate) fn fix_user_ty_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&self, t: T) -> T {
        let t = t.fold_with(&mut FixingRegionReplacer {
            ctx: self.interned,
            f: |r| self.user_region_to_region(r).unwrap_or(self.tcx.lifetimes.re_erased),
        });
        normalize(self, t)
    }

    fn make_relation(&self, iter: impl Iterator<Item = (State, State)>) -> RegionRelation {
        let n = self.base_states.len();
        // make 'static outlive everything
        let iter = iter.chain(State::range(n).map(|n| (STATIC_STATE, n)));
        RegionRelation::new(self.base_states.len(), iter)
    }

    pub(super) fn state_to_name(&self, idx: State) -> Symbol {
        self.base_states[idx].get_name().unwrap_or(Symbol::intern("'_"))
    }

    fn is_logic(&self) -> bool {
        matches!(self.fn_type, FnType::Logic { .. })
    }
}

impl<'a, 'tcx> PreCtx<'a, 'tcx> {
    pub(crate) fn new(interned: &'a InternedInfo<'tcx>, owner_id: DefId) -> Self {
        PreCtx { base: BaseCtx::new(interned, owner_id) }
    }

    pub(super) fn home_to_region(&mut self, s: Symbol) -> Region<'tcx> {
        if let Some(x) = self.try_home_to_region(s) {
            return x;
        }
        let idx = self.base.base_states.push(dummy_region(self.tcx, s));
        // homes that are not declared
        StateSet::singleton(idx).into_region(self.tcx)
    }

    /// Fixes an external region by converting it into a singleton set
    pub(super) fn fix_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        if r.get_name() == Some(self.curr_sym) {
            return self.curr_region();
        }
        let idx = match try_index_of(&self.base_states, &r) {
            Some(idx) => idx,
            None => self.base.base_states.push(r),
        };
        StateSet::singleton(idx).into_region(self.tcx)
    }

    pub(super) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&mut self, t: T) -> T {
        let t = t
            .fold_with(&mut FixingRegionReplacer { ctx: self.interned, f: |r| self.fix_region(r) });
        normalize(&*self, t)
    }

    pub(super) fn finish_for_logic(
        self,
        iter: impl Iterator<Item = (Region<'tcx>, Ty<'tcx>)>,
        bounds: impl Iterator<Item = Outlives>,
    ) -> Ctx<'a, 'tcx> {
        let mut valid_states = StateSet::singleton(CURR_STATE.into());
        let reg_to_idx = |r: Region| StateSet::from(r).try_into_singleton().unwrap();
        let iter = iter
            .flat_map(|(state, ty)| {
                let state_idx = reg_to_idx(state);
                valid_states = valid_states.union(StateSet::singleton(state_idx));
                ty_regions(ty.ty).into_iter().map(move |r| (reg_to_idx(r), state_idx))
            })
            .chain(bounds.filter_map(|b| {
                let home = b.long;
                let long = reg_to_idx(self.try_home_to_region(home)?);
                let home = b.short;
                let short = reg_to_idx(self.try_home_to_region(home)?);
                Some((long, short))
            }));
        let relation = self.base.make_relation(iter);
        let base = BaseCtx { fn_type: FnType::Logic { valid_states }, ..self.base };
        Ctx { base, relation }
    }
}

impl<'a, 'tcx> Ctx<'a, 'tcx> {
    pub(super) fn new_for_spec(
        interned: &'a InternedInfo<'tcx>,
        owner_id: DefId,
    ) -> CreusotResult<Self> {
        let tcx = interned.tcx;
        let mut res = BaseCtx::new(interned, owner_id);
        res.fn_type = FnType::Program;
        let (rs, constraints) = super::variance::constraints_of_fn(tcx, owner_id.expect_local());
        let mut cur_region = None;

        // Add all regions (if any of them are 'curr replace the curr_region instead
        let curr_sym = res.curr_sym;
        res.base_states.extend(rs.filter_map(|x| {
            if x.get_name() == Some(curr_sym) {
                cur_region = Some(x);
                None
            } else {
                Some(x)
            }
        }));
        if let Some(cur_region) = cur_region {
            res.base_states[CURR_STATE] = cur_region
        }

        let mut failed = false;
        let reg_to_idx = |r| index_of(&res.base_states, &r);
        let mut assert_not_curr = |r: Region<'tcx>| {
            if r.get_name() == Some(res.curr_sym) {
                failed = true;
            };
            r
        };
        let constraints = constraints
            .map(|c| match c {
                Constraint::VarSubReg(_, r1) => (reg_to_idx(assert_not_curr(r1)), CURR_STATE),
                Constraint::RegSubReg(r2, r1) => (reg_to_idx(assert_not_curr(r1)), reg_to_idx(r2)),
                _ => (CURR_STATE, CURR_STATE),
            })
            .chain(iter::once((CURR_STATE, OLD_STATE)));
        let relation = res.make_relation(constraints);
        if failed {
            return Err(Error::new(
                tcx.def_ident_span(owner_id).unwrap(),
                format!("{CURR_STR} region must not be blocked"),
            ));
        }
        Ok(Ctx { base: res, relation })
    }

    pub(super) fn curr_home(&self) -> Home {
        self.curr_sym.into()
    }

    /// Fixes an external region by converting it into a singleton set
    pub(super) fn fix_region(&self, r: Region<'tcx>) -> Region<'tcx> {
        if r.is_erased() {
            return StateSet::UNIVERSE.into_region(self.tcx);
        }
        let idx = index_of(&self.base_states, &r);
        let res = StateSet::singleton(idx);
        if self.relation.state_outlived_by(CURR_STATE.into(), res) || self.is_logic() {
            res.into_region(self.tcx)
        } else {
            self.curr_region()
        }
    }

    pub(super) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&self, t: T) -> T {
        let t = t
            .fold_with(&mut FixingRegionReplacer { ctx: self.interned, f: |r| self.fix_region(r) });
        normalize(&*self, t)
    }

    pub(crate) fn try_move_state(&self, state: Region<'tcx>, span: Span) -> CreusotResult<()> {
        if state == self.tcx.lifetimes.re_erased {
            return Err(Error::new(span, "at_expiry must be given an explicit region"));
        } else if state == self.static_region() {
            return Err(Error::new(span, "Cannot move to 'static since it never expires"));
        }

        let dstate = prepare_display(state, self);
        let state = StateSet::from(state);
        if state.try_into_singleton().is_none() {
            return Err(Error::new(span, format!("Cannot move to state set {dstate}")));
        };
        match self.fn_type {
            FnType::Logic { valid_states } if !state.subset(valid_states) => {
                Err(Error::new(span, format!("Cannot move to the state set {dstate} since it might have been instantiated with multiple states")))
            }
            _ => Ok(()),
        }
    }
}

pub(crate) type CtxRef<'a, 'tcx> = &'a Ctx<'a, 'tcx>;
