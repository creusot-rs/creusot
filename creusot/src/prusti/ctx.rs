use crate::error::{CreusotResult, Error};

use super::region_set::*;
use crate::prusti::{
    fn_sig_binder::FnSigBinder,
    parsing::Outlives,
    typeck::{normalize, reg_to_span},
    types::{display_state, prepare_display, Ty},
    util::name_to_def_id,
    variance::{regions_in_arg, regions_of_fn},
    zombie::{fixing_replace, ZombieDefIds},
};
use rustc_index::{bit_set::BitSet, Idx, IndexVec};
use rustc_infer::infer::region_constraints::Constraint;
use rustc_lint::Lint;
use rustc_middle::{
    bug, ty,
    ty::{
        walk::TypeWalker, BoundRegionKind, GenericArgsRef, ParamEnv, Region, TyCtxt, TypeFoldable,
    },
};
use rustc_span::{
    def_id::{DefId, LocalDefId, CRATE_DEF_ID},
    Span, Symbol, DUMMY_SP,
};
use std::{
    fmt::{Debug, Formatter},
    iter,
    ops::Deref,
};

const POST_STR: &str = "'post";
const PRE_STR: &str = "'pre";
const NOW_STR: &str = "'now";

pub(super) const PRE_STATE: State = State(2);
pub(super) const STATIC_STATE: State = State(0);

pub(super) const POST_STATE: State = State(1);
pub(super) const NOW_STATE: State = State(1);

#[derive(Debug)]
enum FnType {
    Logic { valid_states: StateSet },
    Program,
}

pub(crate) struct InternedInfo<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub pre_sym: Symbol,
    pub post_sym: Symbol,
    pub now_sym: Symbol,
    pub pre_display_reg: Region<'tcx>,
    pub post_display_reg: Region<'tcx>,
    pub now_display_reg: Region<'tcx>,
    pub zombie_info: ZombieDefIds,
    pub(super) plain_def_id: DefId,
}

pub(crate) struct BaseCtx<'a, 'tcx> {
    pub interned: &'a InternedInfo<'tcx>,
    base_states: IndexVec<State, Region<'tcx>>,
    pub(super) owner_id: LocalDefId,
    param_env: ParamEnv<'tcx>,
    fn_type: FnType,
    snap_eq_vars: BitSet<u32>,
}

impl<'a, 'tcx> Deref for BaseCtx<'a, 'tcx> {
    type Target = InternedInfo<'tcx>;

    fn deref(&self) -> &Self::Target {
        self.interned
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
    Region::new_late_param(tcx, def_id, BoundRegionKind::BrNamed(def_id, sym))
}

fn try_index_of<I: Idx, T: Eq>(s: &IndexVec<I, T>, x: &T) -> Option<I> {
    Some(s.iter_enumerated().find(|&(_, y)| x == y)?.0)
}

fn index_of<I: Idx, T: Eq + Debug>(s: &IndexVec<I, T>, x: &T) -> I {
    try_index_of(s, x).unwrap_or_else(|| panic!("{s:?} did not contain {x:?}"))
}

fn ty_regions<'tcx>(ty: ty::Ty<'tcx>) -> impl Iterator<Item = Region<'tcx>> {
    TypeWalker::new(ty.into()).filter_map(|x| x.as_region())
}

impl<'tcx> InternedInfo<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Self {
        let syms = [PRE_STR, POST_STR, NOW_STR].map(Symbol::intern);
        let regions = syms.map(|x| dummy_region(tcx, x));
        Self {
            tcx,
            pre_sym: syms[0],
            post_sym: syms[1],
            now_sym: syms[2],
            pre_display_reg: regions[0],
            post_display_reg: regions[1],
            now_display_reg: regions[2],
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
        self.tcx.node_span_lint(lint, hir_id, span, |diag| {
            diag.primary_message(msg.into());
        });
    }

    fn new(
        interned: &'a InternedInfo<'tcx>,
        sig: FnSigBinder<'tcx>,
        logic: bool,
    ) -> CreusotResult<Self> {
        let (base_states, fn_type) = if logic {
            (
                IndexVec::from_iter([interned.tcx.lifetimes.re_static, interned.now_display_reg]),
                FnType::Logic { valid_states: StateSet::EMPTY },
            )
        } else {
            (
                IndexVec::from_iter([
                    interned.tcx.lifetimes.re_static,
                    interned.post_display_reg,
                    interned.pre_display_reg,
                ]),
                FnType::Program,
            )
        };
        let tcx = interned.tcx;
        let base = sig.param_env();
        let fixed = fixing_replace(interned, |r| r, base);
        let erased = tcx.erase_regions(fixed);
        let snap_eq_vars = interned.zombie_info.find_snap_eq_vars(erased, sig.subst().len());
        let mut res = BaseCtx {
            interned,
            base_states,
            owner_id: sig.def_id(),
            fn_type,
            param_env: erased,
            snap_eq_vars,
        };
        // Add all regions (if any of them are 'curr replace the curr_region instead
        let rs = regions_of_fn(tcx, sig);
        for r in rs {
            let span = reg_to_span(tcx, r);
            if let Some(s) = res.builtin_state(r.get_name_or_anon(), span)? {
                res.base_states[s] = r;
            } else {
                res.base_states.push(r);
            }
        }
        Ok(res)
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

    pub(crate) fn pre_state(&self, span: Span) -> CreusotResult<State> {
        if self.is_logic() {
            Err(Error::new(
                span,
                format!("{PRE_STR} can only be used in specifications of program functions"),
            ))
        } else {
            Ok(PRE_STATE)
        }
    }

    pub(crate) fn post_state(&self, span: Span) -> CreusotResult<State> {
        if self.is_logic() {
            Err(Error::new(
                span,
                format!("{POST_STR} can only be used in specifications of program functions"),
            ))
        } else {
            Ok(POST_STATE)
        }
    }

    pub(crate) fn now_state(&self, span: Span) -> CreusotResult<State> {
        if self.is_logic() {
            Ok(NOW_STATE)
        } else {
            Err(Error::new(
                span,
                format!("{NOW_STR} can not be used in specifications of program functions"),
            ))
        }
    }

    pub(crate) fn builtin_state(&self, s: Symbol, span: Span) -> CreusotResult<Option<State>> {
        if s == self.now_sym {
            Ok(Some(self.now_state(span)?))
        } else if s == self.pre_sym {
            Ok(Some(self.pre_state(span)?))
        } else if s == self.post_sym {
            Ok(Some(self.post_state(span)?))
        } else {
            Ok(None)
        }
    }
}

impl<'a, 'tcx> PreCtx<'a, 'tcx> {
    pub(super) fn new(
        interned: &'a InternedInfo<'tcx>,
        sig: FnSigBinder<'tcx>,
    ) -> CreusotResult<Self> {
        Ok(PreCtx { base: BaseCtx::new(interned, sig, true)? })
    }

    fn try_home_to_state(&self, s: Symbol, span: Span) -> CreusotResult<Option<State>> {
        if let Some(s) = self.builtin_state(s, span)? {
            return Ok(Some(s));
        }

        for (idx, reg) in self.base_states.iter_enumerated() {
            if Some(s) == reg.get_name() {
                return Ok(Some(idx));
            }
        }
        Ok(None)
    }

    pub(super) fn home_to_state(&mut self, s: Symbol, span: Span) -> CreusotResult<State> {
        if let Some(x) = self.try_home_to_state(s, span)? {
            return Ok(x);
        }
        // homes that are not declared
        Ok(self.base.base_states.push(dummy_region(self.tcx, s)))
    }

    /// Fixes an external region by converting it into a singleton set
    fn fix_region(&self, r: Region<'tcx>) -> Region<'tcx> {
        let Some(state) = try_index_of(&self.base_states, &r) else { bug!() };
        self.state_to_reg(state)
    }

    pub(crate) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(&self, t: T) -> T {
        let t = fixing_replace(self.interned, |r| self.fix_region(r), t);
        normalize(self, t)
    }

    pub(super) fn finish_for_logic(
        self,
        iter: impl Iterator<Item = (State, Ty<'tcx>)>,
        bounds: impl Iterator<Item = Outlives>,
    ) -> Ctx<'a, 'tcx> {
        let mut valid_states = StateSet::singleton(NOW_STATE);
        let reg_to_idx = |r| StateSet::from(r).try_into_singleton().unwrap();
        let iter = iter
            .flat_map(|(state, ty)| {
                valid_states = valid_states.union(StateSet::singleton(state));
                ty_regions(ty.ty).map(move |r| (reg_to_idx(r), state))
            })
            .chain(bounds.filter_map(|b| {
                let long = self.try_home_to_state(b.long, DUMMY_SP).ok().flatten()?;
                let short = self.try_home_to_state(b.short, DUMMY_SP).ok().flatten()?;
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
        let res = BaseCtx::new(interned, sig, false)?;
        let constraints = super::variance::constraints_of_fn(tcx, sig);

        if regions_in_arg(sig.ty(tcx)).any(|x| x.get_name() == Some(interned.pre_sym)) {
            return Err(Error::new(
                tcx.def_ident_span(sig.def_id()).unwrap(),
                format!("{PRE_STR} region must not appear in program function signature types"),
            ));
        }

        let mut failed = false;
        let reg_to_idx = |r| index_of(&res.base_states, &r);
        let mut assert_not_curr = |r: Region<'tcx>| {
            if r.get_name() == Some(res.post_sym) {
                failed = true;
            };
            r
        };
        let constraints = constraints
            .map(|c| match c {
                Constraint::VarSubReg(_, r1) => (reg_to_idx(assert_not_curr(r1)), POST_STATE),
                Constraint::RegSubReg(r2, r1) => (reg_to_idx(assert_not_curr(r1)), reg_to_idx(r2)),
                _ => (POST_STATE, POST_STATE),
            })
            .chain(iter::once((POST_STATE, PRE_STATE)));
        let relation = res.make_relation(constraints);
        if failed {
            return Err(Error::new(
                tcx.def_ident_span(sig.def_id()).unwrap(),
                format!("{POST_STR} region must not be blocked"),
            ));
        }
        Ok(Ctx { base: res, relation })
    }

    pub(super) fn normalize_state(&self, s: State) -> State {
        let res = StateSet::singleton(s);
        if self.is_logic() || self.relation.outlives_state(res, POST_STATE) || s == PRE_STATE {
            s
        } else {
            // s was not blocked
            POST_STATE
        }
    }

    /// Fixes an external region by converting it into a singleton set
    fn fix_region(&self, r: Region<'tcx>, or: impl Fn() -> Region<'tcx>) -> Region<'tcx> {
        let Some(base_state) = try_index_of(&self.base_states, &r) else { return or() };
        let state = self.normalize_state(base_state);
        self.state_to_reg(state)
    }

    pub fn fix_subst_with_erased(&self, subst: GenericArgsRef<'tcx>) -> GenericArgsRef<'tcx> {
        self.fix_regions(subst, || self.tcx.lifetimes.re_erased)
    }

    pub(super) fn fix_regions<T: TypeFoldable<TyCtxt<'tcx>>>(
        &self,
        t: T,
        or: impl Fn() -> Region<'tcx>,
    ) -> T {
        let t = fixing_replace(self.interned, |r| self.fix_region(r, &or), t);
        normalize(self, t)
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
            return Err(Error::new(span, "at must be given an explicit region"));
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

    pub(super) fn snap_eq_var(&self, v: u32) -> bool {
        if self.is_logic() {
            self.snap_eq_vars.contains(v)
        } else {
            true
        }
    }
}

pub(crate) type CtxRef<'a, 'tcx> = &'a Ctx<'a, 'tcx>;
