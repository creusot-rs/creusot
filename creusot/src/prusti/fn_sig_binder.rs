use rustc_middle::ty::{Binder, FnSig, GenericArgs, GenericArgsRef, ParamEnv, Ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

#[derive(Copy, Clone, Debug)]
pub(crate) struct FnSigBinder<'tcx> {
    def_id: LocalDefId,
    subst: GenericArgsRef<'tcx>,
    sig: Binder<'tcx, FnSig<'tcx>>,
    param_env: ParamEnv<'tcx>,
}

impl<'tcx> FnSigBinder<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        let def_id = def_id.expect_local();
        FnSigBinder {
            def_id,
            subst: GenericArgs::identity_for_item(tcx, def_id),
            sig: tcx.fn_sig(def_id).instantiate_identity(),
            param_env: tcx.param_env(def_id),
        }
    }

    pub(crate) fn for_trait_impl(
        tcx: TyCtxt<'tcx>,
        trait_id: DefId,
        impl_id: DefId,
        subst: GenericArgsRef<'tcx>,
    ) -> Self {
        let def_id = impl_id.expect_local();
        let sig = tcx.fn_sig(trait_id).instantiate(tcx, subst);
        FnSigBinder { def_id, subst, sig, param_env: tcx.param_env(impl_id) }
    }

    pub(super) fn def_id(self) -> LocalDefId {
        self.def_id
    }

    pub(super) fn subst(self) -> GenericArgsRef<'tcx> {
        self.subst
    }

    pub(super) fn sig(self) -> Binder<'tcx, FnSig<'tcx>> {
        self.sig
    }

    pub(super) fn param_env(self) -> ParamEnv<'tcx> {
        self.param_env
    }

    pub(super) fn ty(self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        let fn_sig = tcx.liberate_late_bound_regions(self.def_id().to_def_id(), self.sig());
        Ty::new_fn_ptr(tcx, Binder::dummy(fn_sig))
    }
}
