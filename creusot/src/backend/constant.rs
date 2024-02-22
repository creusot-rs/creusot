use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Const, GenericArgs};

use crate::{
    ctx::TranslatedItem,
    translation::{constant::from_ty_const, fmir::LocalDecls},
};

use super::{
    clone_map::{CloneMap, CloneSummary},
    signature::signature_of,
    CloneDepth, Why3Generator,
};

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn translate_constant(
        &mut self,
        def_id: DefId,
    ) -> (TranslatedItem, CloneSummary<'tcx>) {
        let subst = GenericArgs::identity_for_item(self.tcx, def_id);
        let uneval = ty::UnevaluatedConst::new(def_id, subst);
        let constant = Const::new(
            self.tcx,
            ty::ConstKind::Unevaluated(uneval),
            self.type_of(def_id).instantiate_identity(),
        );

        let param_env = self.param_env(def_id);
        let span = self.def_span(def_id);
        let res = from_ty_const(&mut self.ctx, constant, param_env, span);
        let mut names = CloneMap::new(self.tcx, def_id.into());
        let _ = res.to_why(self, &mut names, &LocalDecls::new());
        let _ = signature_of(self, &mut names, def_id);
        let (_, summary) = names.to_clones(self, CloneDepth::Shallow);

        (TranslatedItem::Constant {}, summary)
    }
}
