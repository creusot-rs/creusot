use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, InternalSubsts};
use why3::declaration::{Decl, LetDecl, LetKind, Module, ValDecl};

use crate::{
    ctx::TranslatedItem,
    translation::{constant::from_ty_const, fmir::LocalDecls, function::closure_generic_decls},
    util::{self, module_name},
};

use super::{
    clone_map::{CloneLevel, CloneMap, CloneSummary},
    logic::stub_module,
    signature::signature_of,
    Why3Generator,
};

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn translate_constant(
        &mut self,
        def_id: DefId,
    ) -> (TranslatedItem, CloneSummary<'tcx>) {
        let subst = InternalSubsts::identity_for_item(self.tcx, def_id);
        let uneval = ty::UnevaluatedConst::new(def_id, subst);
        let constant = self
            .mk_const(ty::ConstKind::Unevaluated(uneval), self.type_of(def_id).subst_identity());

        let param_env = self.param_env(def_id);
        let span = self.def_span(def_id);
        let res = from_ty_const(&mut self.ctx, constant, param_env, span);
        let mut names = CloneMap::new(self.tcx, def_id, CloneLevel::Body);
        let res = res.to_why(self, &mut names, &LocalDecls::new());
        let sig = signature_of(self, &mut names, def_id);
        let mut decls: Vec<_> = closure_generic_decls(self.tcx, def_id).collect();
        let (clones, summary) = names.to_clones(self);
        decls.extend(clones);
        if !util::is_trusted(self.tcx, def_id) {
            decls.push(Decl::Let(LetDecl {
                kind: Some(LetKind::Constant),
                sig: sig.clone(),
                rec: false,
                ghost: false,
                body: res,
            }));
        } else {
            decls.push(Decl::ValDecl(ValDecl {
                ghost: false,
                val: true,
                kind: Some(LetKind::Constant),
                sig,
            }))
        }

        let stub = stub_module(self, def_id);

        let modl = Module { name: module_name(self.tcx, def_id), decls };
        (TranslatedItem::Constant { stub, modl }, summary)
    }
}
