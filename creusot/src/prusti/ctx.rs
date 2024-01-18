use crate::error::{CreusotResult, Error};

use super::{parsing::Home, region_set::*};
use crate::prusti::{
    fn_sig_binder::FnSigBinder,
    parsing::Outlives,
    typeck::normalize,
    types::{display_state, prepare_display, Ty},
    util::name_to_def_id,
    variance::regions_of_fn,
    zombie::{fixing_replace, ZombieDefIds},
};
use rustc_index::{Idx, IndexVec};
use rustc_infer::infer::region_constraints::Constraint;
use rustc_lint::Lint;
use rustc_middle::{
    bug, ty,
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

const CURR_STR: &str = "'curr";
const OLD_STR: &str = "'old";

pub(crate) const OLD_STATE: State = State(0);
pub(crate) const STATIC_STATE: State = State(1);
pub(crate) const CURR_STATE: State = State(2);

#[derive(Debug)]
enum FnType {
    Logic { valid_states: StateSet },
    Program,
}

pub(crate) struct InternedInfo<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub curr_sym: Symbol,
    pub zombie_info: ZombieDefIds,
    pub(super) plain_def_id: DefId,
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
            zombie_info: ZombieDefIds::new(tcx),
            plain_def_id: name_to_def_id(tcx, "prusti_plain"),
        }
    }

    pub(crate) fn mk_region(&self, rs: StateSet) -> Region<'tcx> {
        rs.into_region(self.tcx)
    }

    pub(crate) fn state_to_reg(&self, state: State) -> Region<'tcx> {
        self.mk_region(StateSet::singleton(state))
    }

    pub(crate) fn old_state(&self) -> State {
        OLD_STATE
    }

    pub(crate) fn curr_state(&self) -> State {
        CURR_STATE
    }

    pub(super) fn static_region(&self) -> Region<'tcx> {
        self.state_to_reg(STATIC_STATE)
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

    fn try_home_to_state(&self, s: Symbol) -> Option<State> {
        if s == self.curr_sym {
            return Some(self.curr_state());
        }
        for (idx, reg) in self.base_states.iter_enumerated() {
            if Some(s) == reg.get_name() {
                return Some(idx);
            }
        }
        None
    }

    fn new(interned: &'a InternedInfo<'tcx>, sig: FnSigBinder<'tcx>) -> Self {
        let tcx = interned.tcx;
        let mut curr_region = dummy_region(tcx, interned.curr_sym);
        let old_region = dummy_region(tcx, Symbol::intern(OLD_STR));
        let mut base_states: IndexVec<_, _> =
            [old_region, tcx.lifetimes.re_static, curr_region].into_iter().collect();
        // Add all regions (if any of them are 'curr replace the curr_region instead
        let rs = regions_of_fn(tcx, sig);
        let curr_sym = interned.curr_sym;
        base_states.extend(rs.filter_map(|x| {
            if x.get_name() == Some(curr_sym) {
                curr_region = x;
                None
            } else {
                Some(x)
            }
        }));
        base_states[CURR_STATE] = curr_region;
        let base = sig.param_env();
        let fixed = fixing_replace(interned, |r| r, base);
        let erased = tcx.erase_regions(fixed);
        BaseCtx {
            interned,
            base_states,
            owner_id: sig.def_id(),
            fn_type: FnType::Logic { valid_states: StateSet::EMPTY },
            param_env: erased,
        }
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
    pub(super) fn new(interned: &'a InternedInfo<'tcx>, sig: FnSigBinder<'tcx>) -> Self {
        PreCtx { base: BaseCtx::new(interned, sig) }
    }

    pub(super) fn home_to_state(&mut self, s: Symbol) -> State {
        if let Some(x) = self.try_home_to_state(s) {
            return x;
        }
        // homes that are not declared
        self.base.base_states.push(dummy_region(self.tcx, s))
    }

    /// Fixes an external region by converting it into a singleton set
    fn fix_region(&self, r: Region<'tcx>) -> Region<'tcx> {
        let Some(state) = try_index_of(&self.base_states, &r) else {
            bug!()
        };
        self.state_to_reg(state)
    }

    pub(crate) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&self, t: T) -> T {
        let t = fixing_replace(self.interned, |r| self.fix_region(r), t);
        normalize(&*self, t)
    }

    pub(super) fn finish_for_logic(
        self,
        iter: impl Iterator<Item = (State, Ty<'tcx>)>,
        bounds: impl Iterator<Item = Outlives>,
    ) -> Ctx<'a, 'tcx> {
        let mut valid_states = StateSet::singleton(CURR_STATE.into());
        let reg_to_idx = |r| StateSet::from(r).try_into_singleton().unwrap();
        let iter = iter
            .flat_map(|(state, ty)| {
                valid_states = valid_states.union(StateSet::singleton(state));
                ty_regions(ty.ty).into_iter().map(move |r| (reg_to_idx(r), state))
            })
            .chain(bounds.filter_map(|b| {
                let long = self.try_home_to_state(b.long)?;
                let short = self.try_home_to_state(b.short)?;
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
        sig: FnSigBinder<'tcx>,
    ) -> CreusotResult<Self> {
        let tcx = interned.tcx;
        let mut res = BaseCtx::new(interned, sig);
        res.fn_type = FnType::Program;
        let constraints = super::variance::constraints_of_fn(tcx, sig);

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
                tcx.def_ident_span(sig.def_id()).unwrap(),
                format!("{CURR_STR} region must not be blocked"),
            ));
        }
        Ok(Ctx { base: res, relation })
    }

    pub(super) fn curr_home(&self) -> Home {
        self.curr_sym.into()
    }

    pub(super) fn normalize_state(&self, s: State) -> State {
        let res = StateSet::singleton(s);
        if self.relation.outlives_state(res, CURR_STATE.into()) || self.is_logic() {
            s
        } else {
            // s was not blocked
            self.curr_state()
        }
    }

    /// Fixes an external region by converting it into a singleton set
    fn fix_region(&self, r: Region<'tcx>, or: impl Fn() -> Region<'tcx>) -> Region<'tcx> {
        let Some(base_state) = try_index_of(&self.base_states, &r) else {
            return or()
        };
        let state = self.normalize_state(base_state);
        self.state_to_reg(state)
    }

    pub(super) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(
        &self,
        t: T,
        or: impl Fn() -> Region<'tcx>,
    ) -> T {
        let t = fixing_replace(self.interned, |r| self.fix_region(r, &or), t);
        normalize(&*self, t)
    }

    pub(crate) fn fix_ty(&self, ty: ty::Ty<'tcx>, or: impl Fn() -> Region<'tcx>) -> Ty<'tcx> {
        Ty { ty: self.fix_regions(ty, or) }
    }

    pub(crate) fn fix_ty_with_absurd(&self, ty: ty::Ty<'tcx>) -> Ty<'tcx> {
        let emp = self.interned.mk_region(StateSet::EMPTY);
        self.fix_ty(ty, || emp)
    }

    pub(crate) fn fix_ty_with_erased(&self, ty: ty::Ty<'tcx>) -> Ty<'tcx> {
        self.fix_ty(ty, || self.tcx.lifetimes.re_erased)
    }

    pub(super) fn try_move_state(&self, state: State, span: Span) -> CreusotResult<()> {
        match self.fn_type {
            FnType::Logic { valid_states } if !StateSet::singleton(state).subset(valid_states) => {
                let dstate = display_state(state, self);
                Err(Error::new(span, format!("Cannot move to the state set {dstate} since it might have been instantiated with multiple states")))
            }
            _ => Ok(()),
        }
    }

    pub(crate) fn try_move_rstate(&self, state: Region<'tcx>, span: Span) -> CreusotResult<State> {
        if state == self.tcx.lifetimes.re_erased {
            return Err(Error::new(span, "at_expiry must be given an explicit region"));
        } else if state == self.static_region() {
            return Err(Error::new(span, "Cannot move to 'static since it never expires"));
        }

        let dstate = prepare_display(state, self);
        let state = StateSet::from(state);
        let Some(s) = state.try_into_singleton() else {
            return Err(Error::new(span, format!("Cannot move to state set {dstate}")));
        };
        self.try_move_state(s, span)?;
        Ok(s)
    }
}

pub(crate) type CtxRef<'a, 'tcx> = &'a Ctx<'a, 'tcx>;
