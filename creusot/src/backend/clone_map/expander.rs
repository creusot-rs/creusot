use indexmap::IndexSet;
use petgraph::graphmap::DiGraphMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{subst::SubstsRef, AliasKind, ParamEnv, Ty, TyKind};

use crate::{backend::ty_inv, translation::traits};

use super::*;

pub(super) struct Expander<'tcx> {
    pub clone_graph: DiGraphMap<DepNode<'tcx>, (CloneLevel, IndexSet<(Kind, SymbolKind)>)>,
    pub clone_map: CloneMap<'tcx>,
}

impl<'tcx> Expander<'tcx> {
    pub fn new(names: CloneMap<'tcx>) -> Self {
        Self { clone_graph: Default::default(), clone_map: names }
    }
    // Update the clone graph with new entries
    pub fn update_graph(&mut self, ctx: &mut Why3Generator<'tcx>, depth: CloneDepth) {
        // Construct a maximal sharing graph for all dependencies.
        // We build edges between each (function, subst) pair, following the call graph
        // Additionally, when the substitution refers to an associated type, we construct
        // a relevant edge.
        //
        // Along the edge, we include the 'original' substitution, which we can use
        // to build the correct substitution.
        //
        let mut i = 0;
        let param_env = self.clone_map.param_env(ctx);
        while i < self.clone_map.names.len() {
            let key = *self.clone_map.names.get_index(i).unwrap().0;

            i += 1;
            trace!("update graph with {:?} (public={:?})", key, self.clone_map.names[&key].level);

            let self_key = self.clone_map.self_key();
            if key != self_key {
                self.add_graph_edge(self_key, key, CloneLevel::Root);
            }

            if self.clone_map.names[&key].kind == Kind::Hidden {
                continue;
            }

            if let Some((did, subst)) = key.did() {
                if traits::still_specializable(ctx.tcx, param_env, did, subst) {
                    self.clone_map.names[&key].opaque();
                }

                if self
                    .clone_map
                    .self_did()
                    .is_some_and(|self_did| !ctx.is_transparent_from(did, self_did))
                {
                    self.clone_map.names[&key].opaque();
                }

                ctx.translate(did);

                if util::is_inv_internal(ctx.tcx, did) && depth == CloneDepth::Deep {
                    let ty = subst.type_at(0);
                    let ty = ctx.try_normalize_erasing_regions(param_env, ty).unwrap_or(ty);
                    self.clone_tyinv(ctx, param_env, ty);
                }

                self.clone_laws(ctx, did, subst, depth);
            }

            self.clone_dependencies(ctx, key);
        }
    }

    fn clone_dependencies(&mut self, ctx: &mut Why3Generator<'tcx>, key: DepNode<'tcx>) {
        let key_public = self.clone_map.names[&key].level;

        if let Some((id, key_subst)) = key.did() {
            if util::item_type(ctx.tcx, id) == ItemType::Type {
                for p in ctx.projections_in_ty(id).to_owned() {
                    let node = self.resolve_dep(
                        ctx,
                        CloneNode::new(ctx.tcx, (p.def_id, p.substs)).subst(ctx.tcx, key),
                    );

                    let is_type = self
                        .clone_map
                        .self_did()
                        .map(|did| util::item_type(ctx.tcx, did) == ItemType::Type)
                        .unwrap_or(false);

                    if !is_type {
                        self.clone_map.insert(node).join_level(key_public);
                        self.add_graph_edge(key, node, CloneLevel::Signature);
                    }
                }
            }

            // Check the substitution for node dependencies on closures
            walk_types(key_subst, |t| {
                let node = match t.kind() {
                    TyKind::Alias(AliasKind::Projection, pty) => {
                        let node = CloneNode::new(ctx.tcx, (pty.def_id, pty.substs));
                        Some(self.resolve_dep(ctx, node))
                    }
                    TyKind::Closure(id, subst) => {
                        // Sketchy... shouldn't we need to do something to subst?
                        Some(CloneNode::new(ctx.tcx, (*id, *subst)))
                    }
                    TyKind::Adt(_, _) => Some(CloneNode::Type(t)),
                    _ => None,
                };

                if let Some(node) = node {
                    self.clone_map.insert(node).join_level(key_public);
                    self.add_graph_edge(key, node, CloneLevel::Signature);
                }
            });
        }

        // let opaque_clone = !matches!(self.clone_level, CloneLevel::Body)
        //     || self.names[&key].opaque == CloneOpacity::Opaque;

        // trace!(
        //     "cloning dependencies of {:?} {:?}, len={:?}",
        //     self.names[&key].kind,
        //     key,
        //     ctx.dependencies(key).map(|d| d.len())
        // );

        for (dep, info) in ctx.dependencies(key).iter().flat_map(|i| i.iter()) {
            trace!("adding dependency {:?} {:?}", dep, info.level);

            let orig = dep;

            let dep = self.resolve_dep(ctx, dep.subst(ctx.tcx, key));

            trace!("inserting dependency {:?} {:?}", key, dep);
            self.clone_map.insert(dep).join_level(key_public.max(info.level));

            // Skip reflexive edges
            if dep == key {
                continue;
            }

            let edge_set = self.add_graph_edge(key, dep, info.level);
            if let Some(sym) = refineable_symbol(ctx.tcx, *orig) {
                edge_set.insert((info.kind, sym));
            }
        }
    }

    fn clone_tyinv(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        param_env: ParamEnv<'tcx>,
        ty: Ty<'tcx>,
    ) {
        let inv_kind = if ty_inv::is_tyinv_trivial(ctx.tcx, param_env, ty, true) {
            TyInvKind::Trivial
        } else {
            TyInvKind::from_ty(ty)
        };

        if let TransId::TyInv(self_kind) = self.clone_map.self_id && self_kind == inv_kind {
            return;
        }

        ctx.translate_tyinv(inv_kind);
        self.clone_map.insert(DepNode::TyInv(ty, inv_kind));
    }

    // Adds a dependency from `user` on `prov` for the symbol `sym`.
    fn add_graph_edge(
        &mut self,
        user: DepNode<'tcx>,
        prov: DepNode<'tcx>,
        level: CloneLevel,
    ) -> &mut IndexSet<(Kind, SymbolKind)> {
        let k1 = &self.clone_map.names[&user].kind;
        let k2 = &self.clone_map.names[&prov].kind;
        trace!("edge {k1:?} = {:?} --> {k2:?} = {:?}", user, prov);

        if let None = self.clone_graph.edge_weight_mut(user, prov) {
            self.clone_graph.add_edge(user, prov, (level, IndexSet::new()));
        };

        &mut self.clone_graph.edge_weight_mut(user, prov).unwrap().1
    }

    fn clone_laws(
        &mut self,
        ctx: &mut TranslationCtx<'tcx>,
        key_did: DefId,
        key_subst: SubstsRef<'tcx>,
        depth: CloneDepth,
    ) {
        let Some(item) = ctx.tcx.opt_associated_item(key_did) else { return };
        let Some(self_did) = self.clone_map.self_did() else { return };

        if depth == CloneDepth::Shallow {
            return;
        }

        // Dont clone laws into the trait / impl which defines them.
        if let Some(self_item) = ctx.tcx.opt_associated_item(self_did)
            && self_item.container_id(ctx.tcx) == item.container_id(ctx.tcx) {
            return;
        }

        // If the function we are cloning into is `#[trusted]` there is no need for laws.
        // Similarily, if it has no body, there will be no proofs.
        if util::is_trusted(ctx.tcx, self_did) || !util::has_body(ctx, self_did) {
            return;
        }

        let tcx = ctx.tcx;
        for law in ctx.laws(item.container_id(tcx)) {
            trace!("adding law {:?} in {:?}", *law, self.clone_map.self_id);

            // No way the substitution is correct...
            let law = self.clone_map.insert(DepNode::new(tcx, (*law, key_subst)));
            law.level = CloneLevel::Body;
        }
    }

    // Given an initial substitution, find out the substituted and resolved version of the dependency `dep`.
    // This will attempt to normalize traits and associated types if the substitution provides enough
    // information.
    fn resolve_dep(&self, ctx: &TranslationCtx<'tcx>, dep: DepNode<'tcx>) -> DepNode<'tcx> {
        let param_env = self.clone_map.param_env(ctx);
        dep.resolve(ctx, param_env).unwrap_or(dep)
    }
}

// Identify the name and kind of symbol which can be refined in a given defid
fn refineable_symbol<'tcx>(tcx: TyCtxt<'tcx>, dep: DepNode<'tcx>) -> Option<SymbolKind> {
    use util::ItemType::*;
    let (def_id, _) = dep.did()?;
    match util::item_type(tcx, def_id) {
        Ghost | Logic => Some(SymbolKind::Function(tcx.item_name(def_id))),
        Predicate => Some(SymbolKind::Predicate(tcx.item_name(def_id))),
        Program => Some(SymbolKind::Val(tcx.item_name(def_id))),
        AssocTy => match tcx.associated_item(def_id).container {
            ty::TraitContainer => Some(SymbolKind::Type(tcx.item_name(def_id))),
            ty::ImplContainer => None,
        },
        Trait | Impl => unreachable!("trait blocks have no refinable symbols"),
        Type => None,
        Constant => Some(SymbolKind::Const(tcx.item_name(def_id))),
        _ => unreachable!(),
    }
}
