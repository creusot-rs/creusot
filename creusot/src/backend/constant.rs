use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Const, GenericArgs};

use crate::{ctx::TranslatedItem, translation::constant::from_ty_const};

use super::{
    clone_map::{CloneSummary, Dependencies},
    signature::signature_of,
    term::lower_pure,
    GraphDepth, Why3Generator,
};

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn translate_constant(
        &mut self,
        def_id: DefId,
    ) -> (TranslatedItem, CloneSummary<'tcx>) {
        let subst = GenericArgs::identity_for_item(self.tcx, def_id);
        let uneval = ty::UnevaluatedConst::new(def_id, subst);
        let constant = Const::new(self.tcx, ty::ConstKind::Unevaluated(uneval));
        let ty = self.tcx.type_of(def_id).instantiate(self.tcx, subst);

        let param_env = self.param_env(def_id);
        let span = self.def_span(def_id);
        let res = from_ty_const(&mut self.ctx, constant, ty, param_env, span);
        let mut names = Dependencies::new(self.tcx, [def_id]);
        let _ = lower_pure(self, &mut names, &res);

        let _ = signature_of(self, &mut names, def_id);
        let (_, summary) = names.provide_deps(self, GraphDepth::Shallow);

        (TranslatedItem::Constant {}, summary)
    }
}
