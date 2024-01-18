use rustc_middle::ty::{Binder, FnSig, InternalSubsts, ParamEnv, SubstsRef, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

#[derive(Copy, Clone, Debug)]
pub(crate) struct FnSigBinder<'tcx> {
    def_id: LocalDefId,
    subst: SubstsRef<'tcx>,
    sig: Binder<'tcx, FnSig<'tcx>>,
    param_env: ParamEnv<'tcx>,
}

impl<'tcx> FnSigBinder<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        let def_id = def_id.expect_local();
        FnSigBinder {
            def_id,
            subst: InternalSubsts::identity_for_item(tcx, def_id),
            sig: tcx.fn_sig(def_id).subst_identity(),
            param_env: tcx.param_env(def_id),
        }
    }

    pub(crate) fn for_trait_impl(
        tcx: TyCtxt<'tcx>,
        trait_id: DefId,
        impl_id: DefId,
        subst: SubstsRef<'tcx>,
    ) -> Self {
        let def_id = impl_id.expect_local();
        let sig = tcx.fn_sig(trait_id).subst(tcx, subst);
        FnSigBinder { def_id, subst, sig, param_env: tcx.param_env(impl_id) }
    }

    pub(super) fn def_id(self) -> LocalDefId {
        self.def_id
    }

    pub(super) fn subst(self) -> SubstsRef<'tcx> {
        self.subst
    }

    pub(super) fn sig(self) -> Binder<'tcx, FnSig<'tcx>> {
        self.sig
    }

    pub(super) fn param_env(self) -> ParamEnv<'tcx> {
        self.param_env
    }
}
