use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    subst::SubstsRef, AssocItemContainer::*, ParamEnv, TraitPredicate, TraitRef, TyCtxt,
};
use rustc_trait_selection::traits::ImplSource;

use why3::declaration::{Decl, Module};
use why3::declaration::{TyDecl, TyDeclKind};

use crate::{rustc_extensions, util};

use crate::ctx::*;
use crate::translation::ty;
use crate::util::{ident_of_ty, is_spec};

impl<'tcx> TranslationCtx<'_, 'tcx> {
    // Translate a trait declaration
    pub fn translate_trait(&mut self, def_id: DefId) {
        if !self.translated_items.insert(def_id) {
            return;
        }

        let mut names = CloneMap::new(self.tcx, def_id, true);
        names.clone_self(def_id);
        // The first predicate is a trait reference so we skip it
        for _super_trait in traits_used_by(self.tcx, def_id).filter(|t| t.def_id() != def_id) {
            // Ensure trait depends on all super traits
            // translate_constraint(self, &mut names, super_trait);
        }

        let mut _has_axioms = false;

        for item in associated_items(self.tcx, def_id) {
            self.translate(item.def_id);
        }

        self.add_trait(def_id, _has_axioms);
    }

    pub fn translate_impl(&mut self, impl_id: DefId) {
        if !self.translated_items.insert(impl_id) {
            return;
        }
        let trait_ref = self.tcx.impl_trait_ref(impl_id).unwrap();
        self.translate_trait(trait_ref.def_id);

        for item in associated_items(self.tcx, impl_id) {
            self.translate(item.def_id);
        }

        // Impl Refinement module
        let mut decls: Vec<_> = own_generic_decls_for(self.tcx, impl_id).collect();
        let trait_assocs = self.tcx.associated_items(trait_ref.def_id);
        let mut names = CloneMap::new(self.tcx, impl_id, true);
        for item in associated_items(self.tcx, impl_id) {
            let subst = InternalSubsts::identity_for_item(self.tcx, item.def_id);
            names.insert(item.def_id, subst);

            decls.extend(own_generic_decls_for(self.tcx, item.def_id));

            let trait_item = trait_assocs
                .find_by_name_and_kind(self.tcx, item.ident, item.kind, trait_ref.def_id)
                .unwrap();
            let s = subst.rebase_onto(self.tcx, impl_id, trait_ref.substs);

            names.insert(trait_item.def_id, s).add_dep(
                self.tcx,
                item.ident.name,
                (item.def_id, subst),
            );
        }

        decls.extend(names.to_clones(self));
        self.add_impl(
            impl_id,
            Module { name: translate_value_id(self.tcx, impl_id).name(), decls },
        );
    }

    pub fn translate_assoc_ty(&mut self, def_id: DefId) -> (Module, CloneSummary<'tcx>) {
        assert_eq!(util::item_type(self.tcx, def_id), ItemType::AssocTy);
        let mut names = CloneMap::new(self.tcx, def_id, true);

        self.translated_items.insert(def_id);

        let mut decls: Vec<_> = all_generic_decls_for(self.tcx, def_id).collect();

        let ty_decl = match self.tcx.associated_item(def_id).container {
            rustc_middle::ty::ImplContainer(_) => names.with_public_clones(|names| {
                let assoc_ty = self.tcx.type_of(def_id);
                TyDeclKind::Alias(ty::translate_ty(self, names, rustc_span::DUMMY_SP, assoc_ty))
            }),
            rustc_middle::ty::TraitContainer(_) => TyDeclKind::Opaque,
        };

        // TODO: Clean up translation of names to handle this automatically
        let name = ident_of_ty(self.tcx.item_name(def_id));
        let ty_decl =
            Decl::TyDecl(TyDecl { ty_name: name.clone(), ty_params: Vec::new(), kind: ty_decl });

        decls.extend(names.to_clones(self));
        decls.push(ty_decl);

        (Module { name: translate_type_id(self.tcx, def_id).name(), decls }, names.summary())
    }
}

pub fn associated_items(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = &AssocItem> {
    tcx.associated_items(def_id)
        .in_definition_order()
        .filter(move |item| !is_spec(tcx, item.def_id))
}

pub fn traits_used_by(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = TraitPredicate> {
    let predicates = tcx.predicates_of(def_id);

    predicates.predicates.iter().filter_map(|(pred, _)| {
        let inner = pred.kind().no_bound_vars().unwrap();
        use rustc_middle::ty::PredicateKind::*;
        match inner {
            Trait(tp) => Some(tp),
            _ => None,
        }
    })
}

use crate::function::{all_generic_decls_for, own_generic_decls_for};
use rustc_middle::ty::subst::InternalSubsts;
use rustc_middle::ty::{AssocItem, Binder};

fn resolve_impl_source_opt(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<ImplSource<'tcx, ()>> {
    let trait_ref = if let Some(assoc) = tcx.opt_associated_item(def_id) {
        match assoc.container {
            ImplContainer(def_id) => tcx.impl_trait_ref(def_id)?,
            TraitContainer(def_id) => TraitRef { def_id, substs },
        }
    } else {
        if tcx.is_trait(def_id) {
            TraitRef { def_id, substs }
        } else {
            return None;
        }
    };

    let trait_ref = Binder::dummy(trait_ref);
    let source = rustc_extensions::codegen::codegen_fulfill_obligation(tcx, (param_env, trait_ref));

    match source {
        Ok(src) => Some(src),
        Err(mut err) => {
            err.cancel();

            return None;
        }
    }
}

pub fn resolve_opt(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    if tcx.is_trait(def_id) {
        resolve_trait_opt(tcx, param_env, def_id, substs)
    } else {
        resolve_assoc_item_opt(tcx, param_env, def_id, substs)
    }
}

pub fn resolve_trait_opt(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    if tcx.is_trait(def_id) {
        debug!("wtf: {:?}, {:?}, {:?}", param_env, def_id, substs);
        let impl_source = resolve_impl_source_opt(tcx, param_env, def_id, substs);
        debug!("impl_source={:?}", impl_source);
        match resolve_impl_source_opt(tcx, param_env, def_id, substs)? {
            ImplSource::UserDefined(impl_data) => Some((impl_data.impl_def_id, impl_data.substs)),
            ImplSource::Param(_, _) => Some((def_id, substs)),
            _ => None,
        }
    } else {
        None
    }
}

use rustc_middle::ty::AssocItemContainer;

pub fn resolve_assoc_item_opt(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    let assoc = tcx.opt_associated_item(def_id)?;

    // If we're given an associated item that is already on an instance,
    // we don't need to resolve at all!
    if let AssocItemContainer::ImplContainer(_) = assoc.container {
        return None;
    }

    let source = resolve_impl_source_opt(tcx, param_env, def_id, substs)?;

    match source {
        ImplSource::UserDefined(impl_data) => {
            let trait_def_id = tcx.trait_id_of_impl(impl_data.impl_def_id).unwrap();
            let trait_def = tcx.trait_def(trait_def_id);
            // Find the id of the actual associated method we will be running
            let leaf_def = trait_def
                .ancestors(tcx, impl_data.impl_def_id)
                .unwrap()
                .leaf_def(tcx, assoc.ident, assoc.kind)
                .unwrap_or_else(|| {
                    panic!("{:?} not found in {:?}", assoc, impl_data.impl_def_id);
                });
            use rustc_trait_selection::infer::TyCtxtInferExt;

            // Translate the original substitution into one on the selected impl method
            let leaf_substs = tcx.infer_ctxt().enter(|infcx| {
                let param_env = param_env.with_reveal_all_normalized(tcx);
                let substs = substs.rebase_onto(tcx, trait_def_id, impl_data.substs);
                let substs = rustc_trait_selection::traits::translate_substs(
                    &infcx,
                    param_env,
                    impl_data.impl_def_id,
                    substs,
                    leaf_def.defining_node,
                );
                infcx.tcx.erase_regions(substs)
            });

            Some((leaf_def.item.def_id, leaf_substs))
        }
        ImplSource::Param(_, _) => Some((def_id, substs)),
        _ => unimplemented!(),
    }
}
