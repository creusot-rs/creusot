use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    subst::SubstsRef, AssocItemContainer::*, AssocKind, GenericPredicates, ParamEnv,
    ToPolyTraitRef, TraitPredicate, TraitRef, TyCtxt,
};
use rustc_trait_selection::traits::ImplSource;

use why3::declaration::{CloneKind, TyDecl, TyDeclKind};
use why3::{
    declaration::{CloneSubst, Decl, DeclClone, Module, ValKind::*},
    mlcfg::Type,
    QName,
};

use crate::translation::pure;
use crate::{ctx, rustc_extensions};

use crate::ctx::*;
use crate::translation::ty::{self, translate_ty};
use crate::util::{ident_of, is_contract};

use rustc_resolve::Namespace;

impl<'tcx> TranslationCtx<'_, 'tcx> {
    // Translate a trait declaration
    pub fn translate_trait(&mut self, def_id: DefId) {
        if !self.translated_items.insert(def_id) {
            return;
        }

        let mut names = CloneMap::new(self.tcx, true);
        names.clone_self(def_id);
        // The first predicate is a trait reference so we skip it
        for super_trait in traits_used_by(self.tcx, def_id).filter(|t| t.def_id() != def_id) {
            // Ensure trait depends on all super traits
            translate_constraint(self, &mut names, super_trait);
        }

        let mut decls: Vec<_> = Vec::new();
        decls.extend(own_generic_decls_for(self.tcx, def_id));
        decls.extend(names.to_clones(self));
        let mut has_axioms = false;

        for item in associated_items(self.tcx, def_id) {
            match item.kind {
                AssocKind::Fn => {
                    if item.defaultness.has_value() {
                        let subst = InternalSubsts::identity_for_item(self.tcx, item.def_id);
                        names.insert_raw(item.def_id, subst).mk_export();
                        decls.extend(names.to_clones(self));
                        continue;
                    }

                    let mut sig = crate::util::signature_of(self, &mut names, item.def_id);
                    decls.extend(crate::translation::function::own_generic_decls_for(
                        self.tcx,
                        item.def_id,
                    ));

                    decls.extend(names.to_clones(self));
                    match crate::util::item_type(self.tcx, item.def_id) {
                        ItemType::Logic => decls.push(Decl::ValDecl(Function { sig })),
                        ItemType::Predicate => {
                            sig.retty = None;
                            decls.push(Decl::ValDecl(Predicate { sig }));
                        }
                        ItemType::Program => {
                            decls.push(Decl::ValDecl(Val { sig }));
                        }
                        ItemType::Pure => {
                            has_axioms = true;
                            decls.extend(pure::declaration(sig));
                        }
                        _ => unreachable!(),
                    }
                }
                AssocKind::Type => {
                    let ty_name: why3::Ident = ty::ty_name(self.tcx, item.def_id).into();
                    decls.extend(names.to_clones(self));
                    decls.push(Decl::TyDecl(TyDecl {
                        ty_name,
                        ty_params: Vec::new(),
                        kind: TyDeclKind::Opaque,
                    }));
                }
                knd => unimplemented!("{:?} - {:?}", def_id, knd),
            }
        }

        let trait_name = translate_trait_name(self.tcx, def_id);

        self.add_trait(def_id, Module { name: trait_name.name(), decls }, has_axioms);
    }

    pub fn translate_impl(&mut self, impl_id: DefId) {
        if !self.translated_items.insert(impl_id) {
            return;
        }
        let trait_ref = self.tcx.impl_trait_ref(impl_id).unwrap();
        self.translate_trait(trait_ref.def_id);

        let mut names = CloneMap::new(self.tcx, true);
        names.clone_self(impl_id);
        let decls =
            names.with_public_clones(|names| self.build_impl_module(names, trait_ref, impl_id));
        let name = translate_value_id(self.tcx, impl_id);

        let modl = Module { name: name.name(), decls };

        let mut names = CloneMap::new(self.tcx, false);
        names.clone_self(impl_id);

        let interface_decls =
            names.with_public_clones(|names| self.build_impl_module(names, trait_ref, impl_id));

        let interface_name = interface_name(self.tcx, impl_id);
        let iface = Module { name: interface_name, decls: interface_decls };
        self.add_impl(impl_id, modl, iface, names.summary());
    }

    fn build_impl_module(
        &mut self,
        names: &mut CloneMap<'tcx>,
        trait_ref: TraitRef<'tcx>,
        impl_id: DefId,
    ) -> Vec<Decl> {
        let mut subst = ctx::base_subst(self, names, trait_ref.def_id, trait_ref.substs);

        let mut assoc_types = Vec::new();
        for assoc in self.tcx.associated_items(impl_id).in_definition_order() {
            match assoc.kind {
                AssocKind::Fn => subst.extend(translate_assoc_function(self, names, assoc)),
                AssocKind::Type => {
                    let assoc_ty = self.tcx.type_of(assoc.def_id);
                    // TODO: Clean up translation of names to handle this automatically
                    let name = ident_of(assoc.ident.name);
                    assoc_types.push(Decl::TyDecl(TyDecl {
                        ty_name: name.clone(),
                        ty_params: Vec::new(),
                        kind: TyDeclKind::Alias(ty::translate_ty(
                            self,
                            names,
                            rustc_span::DUMMY_SP,
                            assoc_ty,
                        )),
                    }));

                    subst.push(CloneSubst::Type(
                        name.clone().into(),
                        Type::TConstructor(QName { module: vec![], name }),
                    ))
                }
                AssocKind::Const => self.crash_and_error(
                    self.tcx.span_of_impl(impl_id).unwrap_or(rustc_span::DUMMY_SP),
                    "Associated constants are not yet supported",
                ),
            }
        }

        let mut decls: Vec<_> = Vec::new();
        decls.extend(all_generic_decls_for(self.tcx, impl_id));
        decls.extend(names.to_clones(self));
        decls.extend(assoc_types);

        decls.push(Decl::Clone(DeclClone {
            name: translate_trait_name(self.tcx, trait_ref.def_id),
            subst,
            kind: CloneKind::Export,
        }));

        decls
    }
}

pub fn associated_items(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = &AssocItem> {
    tcx.associated_items(def_id)
        .in_definition_order()
        .filter(move |item| !is_contract(tcx, item.def_id))
}

pub fn translate_predicates(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    preds: GenericPredicates<'tcx>,
) {
    for (pred, _) in preds.predicates.iter() {
        use rustc_middle::ty::PredicateKind::*;
        match pred.kind().no_bound_vars().unwrap() {
            Trait(tp) => translate_constraint(ctx, names, tp),
            Projection(pp) => {
                let _ty = translate_ty(ctx, names, rustc_span::DUMMY_SP, pp.ty);
                names
                    .insert(pp.projection_ty.trait_def_id(ctx.tcx), pp.projection_ty.substs)
                    .add_projection((pp.projection_ty.item_def_id, pp.ty));
            }
            _ => continue,
        }
    }
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

pub fn translate_constraint<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    tp: TraitPredicate<'tcx>,
) {
    names.insert(tp.def_id(), tp.trait_ref.substs);

    // If we haven't seen this trait, first translate it
    ctx.translate_trait(tp.def_id());
}

use crate::function::{all_generic_decls_for, own_generic_decls_for};
use rustc_middle::ty::subst::InternalSubsts;
use rustc_middle::ty::AssocItem;

fn translate_assoc_function(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &'a mut CloneMap<'tcx>,
    assoc: &AssocItem,
) -> impl Iterator<Item = CloneSubst> + 'tcx {
    let impl_id = ctx.tcx.impl_of_method(assoc.def_id).unwrap();
    let trait_id = ctx.tcx.trait_id_of_impl(impl_id).unwrap();

    let assoc_subst = InternalSubsts::identity_for_item(ctx.tcx, impl_id);
    let name = names.insert_raw(assoc.def_id, assoc_subst);
    name.mk_export();
    let name = name.clone();

    ctx.translate_function(assoc.def_id);

    let tcx = ctx.tcx;

    // Get the id of the generic version of the trait method
    let trait_method = tcx
        .associated_items(trait_id)
        .find_by_name_and_namespace(
            ctx.tcx,
            assoc.ident,
            Namespace::ValueNS, //TODO generalize this to include associated types
            trait_id,
        )
        .unwrap();

    // build the substitution between the concrete and generic versions
    let method_subst = tcx
        .generics_of(trait_method.def_id)
        .params
        .iter()
        .zip(tcx.generics_of(assoc.def_id).params.iter())
        .map(move |(tr_param, inst_param)| {
            CloneSubst::Type(
                (&*tr_param.name.as_str().to_lowercase()).into(),
                Type::TConstructor(name.qname(tcx, inst_param.def_id)),
            )
        });

    let name = names.insert_raw(assoc.def_id, assoc_subst);
    let assoc_method = match crate::util::item_type(ctx.tcx, assoc.def_id) {
        ItemType::Logic => {
            CloneSubst::Function(assoc.ident.to_string().into(), name.qname(ctx.tcx, assoc.def_id))
        }
        ItemType::Predicate => {
            CloneSubst::Predicate(assoc.ident.to_string().into(), name.qname(ctx.tcx, assoc.def_id))
        }
        ItemType::Program => {
            CloneSubst::Val(assoc.ident.to_string().into(), name.qname(ctx.tcx, assoc.def_id))
        }
        ItemType::Pure => todo!("pure functions in traits are unimplemented"),
        _ => unreachable!(),
    };

    method_subst.chain(std::iter::once(assoc_method))
}

fn translate_trait_name(tcx: TyCtxt<'_>, def_id: DefId) -> QName {
    translate_value_id(tcx, def_id)
}

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

    let trait_ref = trait_ref.to_poly_trait_ref();
    let source = rustc_extensions::codegen::codegen_fulfill_obligation(tcx, (param_env, trait_ref));

    match source {
        Ok(src) => Some(src),
        Err(mut err) => {
            err.cancel();
            return None;
        }
    }
}

use rustc_span::symbol::Symbol;
// Represents a function applied to a specific, possibly generic substitution, but allows
// us to gracefully smooth over default methods not existing.
// TODO: make the fields private and expose a better api
#[derive(Debug)]
pub struct MethodInstance<'tcx> {
    /// This is the finalizer of the method in rustc parlance, it is not necessarily the method id.
    /// If the method is provided by a default, this would be the instance that is defaulting.
    pub def_id: DefId,
    pub substs: SubstsRef<'tcx>,
    pub ident: Symbol,
}

impl<'tcx> MethodInstance<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, substs: SubstsRef<'tcx>) -> Self {
        Self { def_id, substs, ident: tcx.item_name(def_id) }
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
        let method = resolve_assoc_item_opt(tcx, param_env, def_id, substs)?;
        Some((method.def_id, method.substs))
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

use super::interface::interface_name;
pub fn resolve_assoc_item_opt(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<MethodInstance<'tcx>> {
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

            if leaf_def.finalizing_node.map(|n| n.def_id()) == Some(leaf_def.defining_node.def_id())
            {
                Some(MethodInstance {
                    def_id: leaf_def.item.def_id,
                    substs: leaf_substs,
                    ident: leaf_def.item.ident.name,
                })
            } else {
                Some(MethodInstance {
                    def_id: impl_data.impl_def_id,
                    substs: impl_data.substs,
                    ident: assoc.ident.name,
                })
            }
        }
        ImplSource::Param(_, _) => Some(MethodInstance { def_id, substs, ident: assoc.ident.name }),
        _ => unimplemented!(),
    }
}
