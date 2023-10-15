use rustc_middle::ty::{Binder, EarlyBinder, FnSig, InternalSubsts, SubstsRef, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

#[derive(Copy, Clone, Debug)]
pub(super) struct FnSigBinder<'tcx> {
    def_id: LocalDefId,
    subst: SubstsRef<'tcx>,
    sig: Binder<'tcx, FnSig<'tcx>>,
}

impl<'tcx> FnSigBinder<'tcx> {
    pub(super) fn new(tcx: TyCtxt<'tcx>, def_id: DefId, subst: Option<SubstsRef<'tcx>>) -> Self {
        let def_id = def_id.expect_local();
        let fn_sig: EarlyBinder<Binder<FnSig>> = tcx.fn_sig(def_id);
        match subst {
            None => FnSigBinder {
                def_id,
                subst: InternalSubsts::identity_for_item(tcx, def_id),
                sig: fn_sig.subst_identity(),
            },
            Some(subst) => FnSigBinder { def_id, subst, sig: fn_sig.subst(tcx, subst) },
        }
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
}
