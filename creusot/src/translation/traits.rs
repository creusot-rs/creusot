use rustc_hir::def_id::DefId;
use rustc_middle::ty::{subst::SubstsRef, AssocItemContainer::*, ParamEnv, TraitRef, TyCtxt};
use rustc_trait_selection::traits::ImplSource;

use why3::declaration::TyDecl;
use why3::declaration::{Decl, Module};

use crate::{rustc_extensions, util};

use crate::ctx::*;
use crate::translation::ty;
use crate::util::{is_law, is_spec};

impl<'tcx> TranslationCtx<'_, 'tcx> {
    // Translate a trait declaration
    pub fn translate_trait(&mut self, def_id: DefId) {
        debug!("translating trait {def_id:?}");
        if !self.translated_items.insert(def_id) {
            return;
        }

        let mut laws = Vec::new();

        for item in associated_items(self.tcx, def_id) {
            self.translate(item.def_id);
            if is_law(self.tcx, item.def_id) {
                laws.push(item.def_id);
            }
        }

        self.add_trait(def_id, laws);
    }

    pub fn translate_impl(&mut self, impl_id: DefId) {
        if !self.translated_items.insert(impl_id) {
            return;
        }
        let trait_ref = self.tcx.impl_trait_ref(impl_id).unwrap();
        self.translate_trait(trait_ref.def_id);

        // Impl Refinement module
        let mut decls: Vec<_> = own_generic_decls_for(self.tcx, impl_id).collect();
        let trait_assocs = self.tcx.associated_items(trait_ref.def_id);
        let mut names = CloneMap::new(self.tcx, impl_id, true);

        let mut laws = Vec::new();
        for item in associated_items(self.tcx, impl_id) {
            self.translate(item.def_id);

            let subst = InternalSubsts::identity_for_item(self.tcx, item.def_id);
            names.insert(item.def_id, subst);

            decls.extend(own_generic_decls_for(self.tcx, item.def_id));

            let trait_item = trait_assocs
                .find_by_name_and_kind(self.tcx, item.ident(self.tcx), item.kind, trait_ref.def_id)
                .unwrap();

            if is_law(self.tcx, trait_item.def_id) {
                laws.push(item.def_id);
            }

            let s = subst.rebase_onto(self.tcx, impl_id, trait_ref.substs);

            names.insert(trait_item.def_id, s).add_dep(
                self.tcx,
                item.ident(self.tcx).name,
                (item.def_id, subst),
            );
        }

        decls.extend(names.to_clones(self));
        self.add_impl(impl_id, laws, Module { name: module_name(self.tcx, impl_id), decls });
    }

    pub fn translate_assoc_ty(&mut self, def_id: DefId) -> (Module, CloneSummary<'tcx>) {
        assert_eq!(util::item_type(self.tcx, def_id), ItemType::AssocTy);
        let mut names = CloneMap::new(self.tcx, def_id, true);

        self.translated_items.insert(def_id);

        let mut decls: Vec<_> = all_generic_decls_for(self.tcx, def_id).collect();
        let name = item_name(self.tcx, def_id);

        let ty_decl = match self.tcx.associated_item(def_id).container {
            rustc_middle::ty::ImplContainer(_) => names.with_public_clones(|names| {
                let assoc_ty = self.tcx.type_of(def_id);
                TyDecl::Alias {
                    ty_name: name.clone(),
                    ty_params: vec![],
                    alias: ty::translate_ty(self, names, rustc_span::DUMMY_SP, assoc_ty),
                }
            }),
            rustc_middle::ty::TraitContainer(_) => {
                TyDecl::Opaque { ty_name: name.clone(), ty_params: vec![] }
            }
        };

        decls.extend(names.to_clones(self));
        decls.push(Decl::TyDecl(ty_decl));

        (Module { name: module_name(self.tcx, def_id), decls }, names.summary())
    }
}

pub fn associated_items(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = &AssocItem> {
    tcx.associated_items(def_id)
        .in_definition_order()
        .filter(move |item| !is_spec(tcx, item.def_id))
}

use crate::function::{all_generic_decls_for, own_generic_decls_for};
use rustc_middle::ty::subst::InternalSubsts;
use rustc_middle::ty::{AssocItem, Binder};

fn resolve_impl_source_opt<'tcx>(
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
        Err(err) => {
            err.cancel();

            return None;
        }
    }
}

pub fn resolve_opt<'tcx>(
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

pub fn resolve_trait_opt<'tcx>(
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

pub fn resolve_assoc_item_opt<'tcx>(
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

    let trait_ref = TraitRef::from_method(tcx, tcx.trait_of_item(def_id).unwrap(), substs);
    use crate::rustc_middle::ty::TypeFoldable;
    let source = resolve_impl_source_opt(tcx, param_env, def_id, substs)?;

    match source {
        ImplSource::UserDefined(impl_data) => {
            let trait_def_id = tcx.trait_id_of_impl(impl_data.impl_def_id).unwrap();
            let trait_def = tcx.trait_def(trait_def_id);
            // Find the id of the actual associated method we will be running
            let leaf_def = trait_def
                .ancestors(tcx, impl_data.impl_def_id)
                .unwrap()
                // .leaf_def(tcx, assoc.ident, assoc.kind)
                .leaf_def(tcx, assoc.def_id)
                .unwrap_or_else(|| {
                    panic!("{:?} not found in {:?}", assoc, impl_data.impl_def_id);
                });
            use rustc_trait_selection::infer::TyCtxtInferExt;

            if !leaf_def.is_final() && trait_ref.still_further_specializable() {
                return Some((def_id, substs));
            }
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
        ImplSource::Closure(impl_data) => Some((impl_data.closure_def_id, impl_data.substs)),
        _ => unimplemented!(),
    }
}
