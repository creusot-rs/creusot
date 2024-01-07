use std::{
    collections::{HashSet, VecDeque},
    fmt::Display,
};

use indexmap::IndexSet;
use petgraph::prelude::DiGraphMap;
use rustc_middle::ty::{InternalSubsts, ParamEnv, TyCtxt};
use rustc_type_ir::{AliasKind, TyKind};
use std::collections::HashMap;

use crate::{
    backend::{
        ty_inv::{self, TyInvKind},
        Why3Generator,
    },
    ctx::TranslationCtx,
    translation::traits,
    util::{self, ItemType},
};

use super::{walk_types, CloneLevel, CloneNode, DepNode};

pub struct DependencyGraph<'tcx> {
    /// We need to know which id this graph is for to avoid causing crashes due to laws since we recursively call `translate`.
    self_id: DepNode<'tcx>,

    param_env: ParamEnv<'tcx>,

    /// A directed graph indicating dependencies between items of Creusot's translation.
    /// An edge from A -> B means that A requires B to be present before it can be loaded in turn
    /// Each edge is labelled with the name that B appears with inside of A
    /// This is only relevant when dealing with associated types.
    pub(crate) clone_graph: DiGraphMap<DepNode<'tcx>, DepNode<'tcx>>,

    /// Each node is associated to a visibility determining which level of cloning a calling context needs to see it
    pub(crate) node_weights: HashMap<DepNode<'tcx>, CloneLevel>,

    /// Items that were explicitly requested by user code. Entries here are from *pre-expansion* clones
    roots: IndexSet<DepNode<'tcx>>,

    /// The level of precision we should expand dependencies up to
    clone_level: CloneLevel,
}

impl Display for DependencyGraph<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?} {:?}", self.self_id, self.clone_level)?;
        for ix in self.clone_graph.nodes() {
            writeln!(f, "  {:?}", ix)?;
        }
        Ok(())
    }
}

struct ExpansionQueue<'tcx>(VecDeque<(DepNode<'tcx>, CloneLevel)>);

impl<'tcx> ExpansionQueue<'tcx> {
    fn queue(&mut self, dep: DepNode<'tcx>, visibility: CloneLevel) {
        // eprintln!("Queueing {dep:?} {visibility:?}");
        self.0.push_back((dep, visibility));
    }

    fn dequeue(&mut self) -> Option<(DepNode<'tcx>, CloneLevel)> {
        self.0.pop_front()
    }
}

impl<'tcx> DependencyGraph<'tcx> {
    pub(crate) fn new(
        self_id: DepNode<'tcx>,
        param_env: ParamEnv<'tcx>,
        clone_level: CloneLevel,
    ) -> Self {
        DependencyGraph {
            self_id,
            param_env,
            clone_graph: Default::default(),
            roots: Default::default(),
            clone_level,
            node_weights: Default::default(),
        }
    }

    fn is_tgt(&self, tcx: TyCtxt<'tcx>) -> bool {
        self.self_id
            .did()
            .and_then(|d| tcx.opt_item_name(d.0))
            .map(|s| s.as_str().contains("inversed"))
            .unwrap_or(false)
    }

    pub(crate) fn add_root(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        dep: DepNode<'tcx>,
        vis: CloneLevel,
    ) {
        // eprintln!("Adding root {dep:?}");
        self.roots.insert(dep);
        self.expand_from(ctx, dep, vis);
        self.add_graph_edge(self.self_id, dep, dep);
    }

    fn expand_from(&mut self, ctx: &mut Why3Generator<'tcx>, dep: DepNode<'tcx>, vis: CloneLevel) {
        let mut queue = ExpansionQueue(VecDeque::new());
        queue.queue(dep, vis);
        // let mut visited: HashSet<_> = self.clone_graph.nodes().collect();

        while let Some((next, vis)) = queue.dequeue() {
            // if self.is_tgt(ctx.tcx) {
            // eprintln!("Checking {next:?} {vis:?}");
            // }

            if Some(&vis) <= self.node_weights.get(&next) {
                continue;
            }

            self.node_weights.insert(next, vis);

            self.expand_node(ctx, next, vis, &mut queue);
        }
    }

    // First: determine the information about a node:
    //  - What visibility is it requested from (influences whether it expands recursively)
    //  - Whether it is opaque

    fn expand_node(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        key: DepNode<'tcx>,
        vis: CloneLevel,
        queue: &mut ExpansionQueue<'tcx>,
    ) {
        if self.clone_level == CloneLevel::Body {
            // eprintln!("Expanding {key:?} {vis:?}");
        }
        self.clone_graph.add_node(key);

        if vis > self.clone_level {
            return;
        };

        // Unfortunately still required as dependencies are populated by translation at the moment.
        if let Some((def_id, _)) = key.did() {
            ctx.translate(def_id);
        };

        self.expand_projections(ctx, key);
        self.expand_subst(ctx.tcx, key);
        self.expand_laws(ctx, key, queue);

        if let Some((def_id, _)) = key.did() &&
        // why this?
          util::is_inv_internal(ctx.tcx, def_id) && self.clone_level == CloneLevel::Body {
          self.expand_tyinv(ctx, key, vis, queue);
        }

        // Determine what dependencies we are actually allowed to see
        let opacity = self.node_opacity(ctx, key);

        if self.clone_level == CloneLevel::Body {
            // eprintln!("Expanding deps {:?}", ctx.dependencies(key));
        }
        for (dep, info) in ctx.dependencies(key).iter().flat_map(|i| i.iter()) {
            if self.clone_level == CloneLevel::Body {
                // eprintln!("adding dependency {:?} {:?}", dep, info.public);
            }

            // If this is *not* a public clone and we are not allowed to look inside the body then continue
            if !info.public && opacity != CloneLevel::Body {
                continue;
            }

            let orig = dep;
            let dep = self.resolve_dep(ctx.tcx, dep.subst(ctx.tcx, key));

            trace!("inserting dependency {:?} {:?}", key, dep);

            // HACK: `info.public` should be directly replaced with a CloneLevel
            let vis = if info.public { CloneLevel::Interface } else { CloneLevel::Body };
            queue.queue(dep, vis);

            self.add_graph_edge(key, dep, *orig);
        }
    }

    // Figure out how far we're allowed to peer into `key`
    fn node_opacity(&self, ctx: &mut TranslationCtx<'tcx>, key: DepNode<'tcx>) -> CloneLevel {
        let Some((did, subst)) = key.did() else { return CloneLevel::Stub };

        if traits::still_specializable(ctx.tcx, self.param_env, did, subst) {
            return CloneLevel::Interface;
        };

        if self.self_id.did().is_some_and(|self_did| !ctx.is_transparent_from(did, self_did.0)) {
            return CloneLevel::Interface;
        };
        // TODO: Change
        return self.clone_level;
    }

    fn expand_projections(&mut self, ctx: &mut Why3Generator<'tcx>, key: DepNode<'tcx>) {
        let Some((id, key_subst)) = key.did() else { return };
        if util::item_type(ctx.tcx, id) != ItemType::Type {
            return;
        }

        for p in ctx.projections_in_ty(id).to_owned() {
            let node = self.resolve_dep(
                ctx.tcx,
                CloneNode::new(ctx.tcx, (p.def_id, p.substs)).subst(ctx.tcx, key),
            );

            let is_type = self
                .self_id
                .did()
                .map(|(did, _)| util::item_type(ctx.tcx, did) == ItemType::Type)
                .unwrap_or(false);

            if !is_type {
                // self.insert(node).public |= key_public;
                // eprintln!("hello?");
                self.add_graph_edge(key, node, node);
            }
        }
    }

    fn expand_subst(&mut self, tcx: TyCtxt<'tcx>, key: DepNode<'tcx>) {
        let Some((_, key_subst)) = key.did() else { return };
        // eprintln!("Expanding subst {key_subst:?}");

        // Check the substitution for node dependencies on closures
        walk_types(key_subst, |t| {
            let node = match t.kind() {
                TyKind::Alias(AliasKind::Projection, pty) => {
                    let node = CloneNode::new(tcx, (pty.def_id, pty.substs));
                    self.resolve_dep(tcx, node)
                }
                TyKind::Closure(id, subst) => {
                    // Sketchy... shouldn't we need to do something to subst?
                    CloneNode::new(tcx, (*id, *subst))
                }
                TyKind::Adt(_, _)
                | TyKind::Param(_)
                | TyKind::Uint(_)
                | TyKind::Int(_)
                | TyKind::Slice(_)
                | TyKind::Array(_, _) => CloneNode::Type(t),
                // _ => CloneNode::Type(t),
                _ => return,
            };

            // eprintln!("adding {node:?}");

            // self.insert(node).public |= key_public;
            self.add_graph_edge(key, node, node);
        });
    }

    fn expand_tyinv(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        key: DepNode<'tcx>,
        vis: CloneLevel,
        queue: &mut ExpansionQueue<'tcx>,
    ) {
        let Some((did, subst)) = key.did() else { return };
        if !util::is_inv_internal(ctx.tcx, did) {
            return;
        };
        let ty = subst.type_at(0);
        let ty = ctx.tcx.try_normalize_erasing_regions(self.param_env, ty).unwrap_or(ty);

        let inv_kind = if ty_inv::is_tyinv_trivial(ctx.tcx, self.param_env, ty, true) {
            TyInvKind::Trivial
        } else {
            TyInvKind::from_ty(ty)
        };

        if let DepNode::TyInv(_, self_kind) = self.self_id && self_kind == inv_kind {
            return;
        }
        ctx.translate_tyinv(inv_kind);

        let node = DepNode::TyInv(ty, inv_kind);
        self.add_graph_edge(self.self_id, node, node);

        queue.queue(node, vis);
    }

    fn expand_laws(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        key: DepNode<'tcx>,
        queue: &mut ExpansionQueue<'tcx>,
    ) {
        let Some((def_id, substs)) = key.did() else { return };
        let Some(item) = ctx.tcx.opt_associated_item(def_id) else { return };
        let Some((self_did, _)) = self.self_id.did() else { return };

        // // Dont clone laws into the trait / impl which defines them.
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
            trace!("adding law {:?} {:?}", law, substs);
            queue.queue(DepNode::new(tcx, (*law, substs)), CloneLevel::Body);
        }
    }

    // Adds a dependency from `user` on `prov` for the symbol `sym`.
    fn add_graph_edge(&mut self, user: DepNode<'tcx>, prov: DepNode<'tcx>, label: DepNode<'tcx>) {
        // let k1 = &self.names[&user].kind;
        // let k2 = &self.names[&prov].kind;
        trace!("edge {:?} --> {:?}", user, prov);
        // if user == prov {
        //     return;
        // }

        if let None = self.clone_graph.edge_weight_mut(user, prov) {
            self.clone_graph.add_edge(user, prov, label);
        };

        self.clone_graph.edge_weight_mut(user, prov).unwrap();
    }

    // Given an initial substitution, find out the substituted and resolved version of the dependency `dep`.
    // This will attempt to normalize traits and associated types if the substitution provides enough
    // information.
    fn resolve_dep(&self, tcx: TyCtxt<'tcx>, dep: DepNode<'tcx>) -> DepNode<'tcx> {
        let param_env = self.param_env;
        dep.resolve(tcx, param_env).unwrap_or(dep)
    }
}
