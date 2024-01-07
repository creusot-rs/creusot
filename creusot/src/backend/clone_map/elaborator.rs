use std::iter;

use indexmap::IndexSet;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::ParamEnv;
use rustc_span::DUMMY_SP;

use why3::{
    declaration::{CloneSubst, Decl, DeclClone, Use},
    QName,
};

use crate::{
    backend::{
        self,
        clone_map::{cloneable_name, CloneOpacity},
        ty::ty_param_names,
        Why3Generator,
    },
    ctx::*,
    util::{self, get_builtin},
};

use super::{DepGraph, DepNode};

/// The `CloneElaborator` is responsible for transforming an individual `DepNode` into a clone,
/// to do this it is provided access to the graph (so it can fill in the dependencies of a clone) and to the `CloneMap`
/// as it needs to translate types which introduces a circularity
pub(super) struct CloneElaborator<'tcx> {
    used_types: IndexSet<DefId>,
    param_env: ParamEnv<'tcx>,
}

impl<'tcx> CloneElaborator<'tcx> {
    pub fn new(param_env: ParamEnv<'tcx>) -> Self {
        Self { used_types: Default::default(), param_env }
    }

    pub fn build_clone(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        // Temporary, turn this parametric
        names: &mut CloneMap<'tcx>,
        // Temporary, turn parametric
        deps: &DepGraph<'tcx>,
        item: DepNode<'tcx>,
        depth: CloneDepth,
    ) -> Option<Decl> {
        // Types can't be cloned, but are used (for now).
        if let DepNode::Type(_) = item {
            let (def_id, _) = item.did()?;
            // check if type is not an assoc type
            if util::item_type(ctx.tcx, def_id) == ItemType::Type {
                let use_decl = self.used_types.insert(def_id).then(|| {
                    if let Some(builtin) = get_builtin(ctx.tcx, def_id) {
                        let name = QName::from_string(&builtin.as_str()).unwrap().module_qname();
                        Use { name, as_: None, export: false }
                    } else {
                        let name = cloneable_name(ctx, item, CloneLevel::Body);
                        Use { name: name.clone(), as_: Some(name), export: false }
                    }
                });
                return use_decl.map(Decl::UseDecl);
            }
        }

        let mut clone_subst = base_subst(ctx, self.param_env, names, item);
        trace!("base substs of {item:?}: {clone_subst:?}");

        let outbound: Vec<_> = deps.dependencies(item).collect();

        let level_of_item = match (depth, deps.info(item).opaque) {
            // We are requesting a deep clone of an opaque thing: stop at the contract
            (CloneDepth::Deep, CloneOpacity::Opaque) => CloneLevel::Contract,
            // Otherwise, go deep and get the body
            (CloneDepth::Deep, _) => CloneLevel::Body,
            // If we are only doing shallow clones, stop at the signature (no contracts)
            (CloneDepth::Shallow, _) => CloneLevel::Signature,
        };

        // Grab definitions from all of our dependencies
        for (edge_level, syms, dep) in outbound {
            if edge_level > level_of_item {
                continue;
            };
            trace!("dependency={:?} of={:?} syms={:?}", dep, item, syms);

            match dep {
                DepNode::Type(ty) => {
                    for (nm, sym) in syms.clone() {
                        let ty_name = nm.qname_ident(sym.ident());
                        let ty = backend::ty::translate_ty(ctx, names, DUMMY_SP, ty);
                        clone_subst.push(CloneSubst::Type(ty_name, ty))
                    }
                }
                _ => {
                    for (nm, sym) in syms {
                        let elem = sym.to_subst(*nm, deps.info(dep).kind);
                        clone_subst.push(elem);
                    }
                }
            }
        }

        let use_axioms = item.is_inv()
            || item.did().is_some_and(|(def_id, _)| {
                ctx.item(def_id).map(|i| i.has_axioms()).unwrap_or(false)
            });

        if use_axioms {
            clone_subst.push(CloneSubst::Axiom(None))
        }

        trace!(
            "emit clone node={item:?} name={:?} as={:?}",
            cloneable_name(ctx, item, level_of_item),
            deps.info(item).kind.clone()
        );

        Some(Decl::Clone(DeclClone {
            name: cloneable_name(ctx, item, level_of_item),
            subst: clone_subst,
            kind: deps.info(item).kind.clone().into(),
        }))
    }
}

pub(crate) fn base_subst<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    param_env: ParamEnv<'tcx>,
    names: &mut N,
    dep: DepNode<'tcx>,
) -> Vec<CloneSubst> {
    let (generics, substs) = if let DepNode::TyInv(ty, inv_kind) = dep {
        let generics = inv_kind.generics(ctx.tcx);
        let substs = inv_kind.tyinv_substs(ctx.tcx, ty);
        (generics, substs)
    } else if let Some((def_id, subst)) = dep.did() {
        let generics = ty_param_names(ctx.tcx, def_id).collect();
        (generics, subst)
    } else {
        return vec![];
    };

    let mut clone_substs = vec![];
    for (name, arg) in iter::zip(generics, substs.types()) {
        let ty = ctx.normalize_erasing_regions(param_env, arg);
        let ty = backend::ty::translate_ty(ctx, names, rustc_span::DUMMY_SP, ty);
        clone_substs.push(CloneSubst::Type(name.into(), ty));
    }
    clone_substs
}
