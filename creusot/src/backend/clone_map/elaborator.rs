use std::iter;

use indexmap::IndexSet;
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{ParamEnv, SubstsRef, Ty};
use rustc_span::DUMMY_SP;
use rustc_target::abi::FieldIdx;

use why3::{
    declaration::{CloneSubst, Decl, DeclClone, LetDecl, Use, ValDecl},
    Ident, QName,
};

use crate::{
    backend::{
        self,
        clone_map::{cloneable_name, CloneOpacity},
        signature::{sig_to_why3, signature_of},
        term::lower_pure,
        ty::ty_param_names,
        Why3Generator,
    },
    ctx::*,
    translation::specification::PreContract,
    util::{self, get_builtin, item_name},
};

use super::{CloneNames, DepGraph, DepNode, Kind};

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
        level_of_item: CloneLevel,
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

        // Grab definitions from all of our dependencies
        for (edge_level, syms, dep) in deps.dependencies(item) {
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

/// The symbol elaborator expands required definitions as symbols and definitions, effectively performing the clones itself.
pub(super) struct SymbolElaborator<'tcx> {
    used_types: IndexSet<DefId>,
    param_env: ParamEnv<'tcx>,
}

impl<'tcx> SymbolElaborator<'tcx> {
    pub fn new(param_env: ParamEnv<'tcx>) -> Self {
        Self { used_types: Default::default(), param_env }
    }

    pub fn build_clone(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        _: &DepGraph<'tcx>,
        item: DepNode<'tcx>,
        level_of_item: CloneLevel,
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

        let Some((def_id, subst)) = item.did() else { unreachable!() };

        let mut pre_sig = ctx.sig(def_id).clone();
        let kind = util::item_type(ctx.tcx, def_id).let_kind();
        // let names = SymNamer(names.names.clone());
        // let names = &mut & names ;

        if CloneLevel::Signature == level_of_item {
            pre_sig.contract = PreContract::default();

            let mut sig = sig_to_why3(ctx, names, pre_sig, def_id);
            sig.name = names.value(def_id, subst).name;
            let val = ValDecl { ghost: false, val: true, kind, sig };

            return Some(Decl::ValDecl(val));
        } else if CloneLevel::Contract == level_of_item {
            let mut sig = sig_to_why3(ctx, names, pre_sig, def_id);
            sig.name = names.value(def_id, subst).name;

            let val = ValDecl { ghost: false, val: true, kind, sig };
            return Some(Decl::ValDecl(val));
        };

        let mut sig = sig_to_why3(ctx, names, pre_sig, def_id);
        eprintln!("cloning {def_id:?} with name {:?}", names.value(def_id, subst));
        eprintln!("  in {:?}", names.self_did());
        eprintln!("{:?}", names.names.names);
        sig.name = names.value(def_id, subst).name;

        if ctx.is_logical(def_id) {
            let term = ctx.term(def_id)?.clone();

            let body = lower_pure(ctx, names, term);

            Some(Decl::Let(LetDecl { kind, sig, rec: false, ghost: false, body }))
        } else {
            let val = ValDecl { ghost: false, val: true, kind, sig };
            Some(Decl::ValDecl(val))
        }
    }
}

// struct SymNamer<'tcx>(CloneNames<'tcx>);

// impl<'tcx> Namer<'tcx> for &SymNamer<'tcx> {
//     fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
//         let node = DepNode::new(self.0.tcx, (def_id, subst));
//         let kind = self.0.names[&node];
//         eprintln!("{def_id:?} {subst:?}");
//         match kind {
//             Kind::Hidden => "foo".into(),
//             Kind::Named(nm) => "bar".into(),
//         }
//     }

//     // Wrong since types are currently still being used under the current model. Once they are also 'cloned' into a module we can make this change
//     fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
//         let node = DepNode::new(self.0.tcx, (def_id, subst));
//         let kind = self.0.names[&node];

//         "type".into()
//         // match kind {
//         //     Kind::Hidden => item_name(self.0.tcx, def_id, Namespace::TypeNS).into(),
//         //     Kind::Named(nm) => Ident::build(nm.as_str()).into(),
//         // }
//     }

//     fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
//         todo!()
//     }

//     fn accessor(
//         &mut self,
//         def_id: DefId,
//         subst: SubstsRef<'tcx>,
//         variant: usize,
//         ix: FieldIdx,
//     ) -> QName {
//         "accessor".into()
//     }

//     fn normalize(&self, _: &TranslationCtx<'tcx>, _: Ty<'tcx>) -> Ty<'tcx> {
//         panic!("Normalization not yet implemented")
//         // self.tcx.try_normalize_erasing_regions(self.param_env(ctx), ty).unwrap_or(ty)
//     }

//     fn import_prelude_module(&mut self, _: PreludeModule) {
//         ()
//     }

//     fn import_builtin_module(&mut self, _: QName) {
//         ()
//     }

//     fn with_vis<F, A>(&mut self, _: CloneLevel, f: F) -> A
//     where
//         F: FnOnce(&mut Self) -> A,
//     {
//         f(self)
//     }
// }
