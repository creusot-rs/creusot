use std::iter;

use heck::ToSnakeCase;
use indexmap::IndexSet;
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
};
use rustc_middle::ty::{self, EarlyBinder, ParamEnv, SubstsRef, Ty, TyCtxt};
use rustc_span::{Symbol, DUMMY_SP};
use rustc_target::abi::FieldIdx;

use why3::{
    declaration::{Axiom, CloneSubst, Decl, DeclClone, LetDecl, Use, ValDecl},
    Ident, QName,
};

use crate::{
    backend::{
        self,
        clone_map::{cloneable_name, CloneOpacity},
        signature::{sig_to_why3, signature_of},
        term::lower_pure,
        ty::ty_param_names,
        ty_inv::{build_inv_axiom, invariant_term},
        Why3Generator,
    },
    ctx::*,
    translation::{pearlite::normalize, specification::PreContract},
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
        let self_key = names.self_key();

        let old_names = names;
        let mut names = SymNamer {
            tcx: ctx.tcx,
            names: old_names.names.clone(),
            param_env: old_names.param_env(ctx),
        };
        let names = &mut names;

        // let names = old_names;

        if let DepNode::TyInv(ty, kind) = item {
            let term = invariant_term(ctx, ty, kind);
            let exp = lower_pure(ctx, names, term);
            let axiom = Axiom { name: names.ty_inv(ty).name, rewrite: false, axiom: exp };
            return Some(Decl::Axiom(axiom));
        }

        let Some((def_id, subst)) = item.did() else { unreachable!() };

        if util::item_type(ctx.tcx, def_id) == ItemType::AssocTy {
            let DepNode::Type(assoc_ty) = item else { panic!() };
            eprintln!("{:?}", self_key);
            eprintln!(
                " associated type for the moment {assoc_ty:?} normalizes to {:?}",
                names.normalize(ctx, assoc_ty)
            );

            return Some(ctx.assoc_ty_decl(names, def_id));
        }

        let mut pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone()).subst(ctx.tcx, subst);
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
        sig.name = names.value(def_id, subst).name;

        if ctx.is_logical(def_id) {
            let term = ctx.term(def_id)?.clone();

            let mut term = EarlyBinder::bind(term).subst(ctx.tcx, subst);
            normalize(ctx.tcx, names.param_env, &mut term);
            let body = lower_pure(ctx, names, term);

            Some(Decl::Let(LetDecl { kind, sig, rec: false, ghost: false, body }))
        } else {
            let val = ValDecl { ghost: false, val: true, kind, sig };
            Some(Decl::ValDecl(val))
        }
    }
}

struct SymNamer<'tcx> {
    tcx: TyCtxt<'tcx>,
    names: CloneNames<'tcx>,
    param_env: ParamEnv<'tcx>,
}

impl<'tcx> SymNamer<'tcx> {
    fn get(&self, ix: DepNode<'tcx>) -> &Kind {
        self.names.names.get(&ix).unwrap_or_else(|| {
            panic!("Could not find {ix:?}");
        })
    }
}

impl<'tcx> Namer<'tcx> for SymNamer<'tcx> {
    fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let name = item_name(self.tcx, def_id, Namespace::ValueNS);
        let node = DepNode::new(self.tcx, (def_id, subst));
        match self.get(node) {
            Kind::Hidden => name.into(),
            Kind::Named(nm) => nm.as_str().to_snake_case().into(),
        }
    }

    fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let name = item_name(self.tcx, def_id, Namespace::TypeNS);
        let node = DepNode::new(self.tcx, (def_id, subst));
        self.get(node).qname_ident(name.into())
    }

    fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let type_id = match self.tcx.def_kind(def_id) {
            DefKind::Closure | DefKind::Struct | DefKind::Enum | DefKind::Union => def_id,
            DefKind::Variant => self.tcx.parent(def_id),
            _ => unreachable!("Not a type or constructor"),
        };
        let mut name = item_name(self.tcx, def_id, Namespace::ValueNS);
        name.capitalize();
        let node = DepNode::new(self.tcx, (type_id, subst));
        self.get(node).qname_ident(name.into())
    }

    /// Creates a name for a type or closure projection ie: x.field1
    /// This also includes projections from `enum` types
    ///
    /// * `def_id` - The id of the type or closure being projected
    /// * `subst` - Substitution that type is being accessed at
    /// * `variant` - The constructor being used. For closures this is always 0
    /// * `ix` - The field in that constructor being accessed.
    fn accessor(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
        variant: usize,
        ix: FieldIdx,
    ) -> QName {
        let tcx = self.tcx;
        let node = DepNode::new(self.tcx, (def_id, subst));
        let clone = self.get(node);
        let name: Ident = match util::item_type(tcx, def_id) {
            ItemType::Closure => format!("field_{}", ix.as_usize()).into(),
            ItemType::Type => {
                let variant_def = &tcx.adt_def(def_id).variants()[variant.into()];
                let variant = variant_def;
                format!(
                    "{}_{}",
                    variant.name.as_str().to_ascii_lowercase(),
                    variant.fields[ix].name
                )
                .into()
            }
            _ => panic!("accessor: invalid item kind"),
        };

        clone.qname_ident(name.into())
    }

    fn ty_inv(&mut self, ty: Ty<'tcx>) -> QName {
        let def_id =
            self.tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = self.tcx.mk_substs(&[ty::GenericArg::from(ty)]);
        self.value(def_id, subst)
    }

    fn normalize(&self, _: &TranslationCtx<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.tcx.try_normalize_erasing_regions(self.param_env, ty).unwrap_or(ty)

        // self.tcx.try_normalize_erasing_regions(self.param_env(ctx), ty).unwrap_or(ty)
    }

    fn import_prelude_module(&mut self, module: PreludeModule) {
        self.import_builtin_module(module.qname());
    }

    fn import_builtin_module(&mut self, module: QName) {
        self.names.prelude.entry(module).or_insert(false);
    }

    fn with_vis<F, A>(&mut self, _: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        // let public = std::mem::replace(&mut self.dep_level, vis);
        let ret = f(self);
        // self.dep_level = public;
        ret
    }
}
