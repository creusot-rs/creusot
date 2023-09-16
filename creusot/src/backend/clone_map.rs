#![allow(deprecated)]

use std::iter;

use heck::ToUpperCamelCase;
use indexmap::{IndexMap, IndexSet};
use petgraph::{graphmap::DiGraphMap, visit::DfsPostOrder, EdgeDirection::Outgoing};
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
};
use rustc_middle::ty::{
    self, subst::SubstsRef, AliasKind, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable,
    TypeSuperVisitable, TypeVisitor,
};
use rustc_span::{Symbol, DUMMY_SP};
use rustc_target::abi::FieldIdx;

use why3::{
    declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use},
    Ident, QName,
};

use crate::{
    backend::{self, dependency::Dependency, interface},
    ctx::*,
    translation::traits,
    util::{self, get_builtin, ident_of, ident_of_ty, inv_module_name, item_name, module_name},
};

// Prelude modules
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PreludeModule {
    Float32,
    Float64,
    Int,
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    Isize,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    Usize,
    Char,
    Bool,
    Borrow,
    Slice,
    Opaque,
    Ref,
    Seq,
    Type,
}

impl PreludeModule {
    fn qname(&self) -> QName {
        match self {
            PreludeModule::Float32 => QName::from_string("prelude.Float32").unwrap(),
            PreludeModule::Float64 => QName::from_string("prelude.Float64").unwrap(),
            PreludeModule::Int => QName::from_string("prelude.Int").unwrap(),
            PreludeModule::Int8 => QName::from_string("prelude.Int8").unwrap(),
            PreludeModule::Int16 => QName::from_string("prelude.Int16").unwrap(),
            PreludeModule::Int32 => QName::from_string("prelude.Int32").unwrap(),
            PreludeModule::Int64 => QName::from_string("prelude.Int64").unwrap(),
            PreludeModule::Int128 => QName::from_string("prelude.Int128").unwrap(),
            PreludeModule::UInt8 => QName::from_string("prelude.UInt8").unwrap(),
            PreludeModule::UInt16 => QName::from_string("prelude.UInt16").unwrap(),
            PreludeModule::UInt32 => QName::from_string("prelude.UInt32").unwrap(),
            PreludeModule::UInt64 => QName::from_string("prelude.UInt64").unwrap(),
            PreludeModule::UInt128 => QName::from_string("prelude.UInt128").unwrap(),
            PreludeModule::Char => QName::from_string("prelude.Char").unwrap(),
            PreludeModule::Opaque => QName::from_string("prelude.Opaque").unwrap(),
            PreludeModule::Ref => QName::from_string("Ref").unwrap(),
            PreludeModule::Seq => QName::from_string("prelude.Seq").unwrap(),
            PreludeModule::Type => QName::from_string("Type").unwrap(),
            PreludeModule::Isize => QName::from_string("prelude.IntSize").unwrap(),
            PreludeModule::Usize => QName::from_string("prelude.UIntSize").unwrap(),
            PreludeModule::Bool => QName::from_string("prelude.Bool").unwrap(),
            PreludeModule::Borrow => QName::from_string("prelude.Borrow").unwrap(),
            PreludeModule::Slice => QName::from_string("prelude.Slice").unwrap(),
        }
    }
}

// a clone node is expected to have a DefId
type CloneNode<'tcx> = Dependency<'tcx>;
type DepNode<'tcx> = Dependency<'tcx>;
pub(super) type CloneSummary<'tcx> = IndexMap<CloneNode<'tcx>, CloneInfo>;

#[derive(Clone)]
pub struct CloneMap<'tcx> {
    tcx: TyCtxt<'tcx>,
    prelude: IndexMap<QName, bool>,
    names: IndexMap<CloneNode<'tcx>, CloneInfo>,

    // Track how many instances of a name already exist
    name_counts: IndexMap<Symbol, usize>,

    // Indicates the desired level of information in clones
    // - Stub: serves purely in logical function definitions to get around the limitations of `clone`
    // - Interface: Will clone only the interface of used modules
    // - Body: Will directly use the full body of dependencies, except for program functions
    clone_level: CloneLevel,

    // TransId of the item which is cloning. Used for trait resolution
    self_id: TransId,
    // TODO: Push the graph into an opaque type with tight api boundary
    // Graph which is used to calculate the full clone set
    clone_graph: DiGraphMap<DepNode<'tcx>, IndexSet<(Kind, SymbolKind)>>,
    // Index of the last cloned entry
    last_cloned: usize,

    // Internal state to determine whether clones should be public or not
    public: bool,

    // Used to ensure we only have a single `use` per type.
    used_types: IndexSet<DefId>,
}

impl<'tcx> Drop for CloneMap<'tcx> {
    fn drop(&mut self) {
        if self.last_cloned != self.names.len() {
            debug!(
                "Dropping clone map with un-emitted clones. {:?} clones emitted of {:?} total {:?}",
                self.last_cloned,
                self.names.len(),
                self.self_id,
            );
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable, Hash)]
enum Kind {
    Named(Symbol),
    Hidden,
    Export,
}

impl Kind {
    pub(crate) fn qname_ident(&self, method: Ident) -> QName {
        let module = match &self {
            Kind::Named(name) => vec![name.to_string().into()],
            _ => Vec::new(),
        };
        QName { module, name: method }
    }
}

use rustc_macros::{TyDecodable, TyEncodable};

use super::{
    ty::ty_param_names,
    ty_inv::{self, TyInvKind},
    TransId, Why3Generator,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
enum CloneOpacity {
    Transparent,
    Opaque,
    Default,
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct CloneInfo {
    kind: Kind,
    cloned: bool,
    public: bool,
    opaque: CloneOpacity,
}

impl Into<CloneKind> for Kind {
    fn into(self) -> CloneKind {
        match self {
            Kind::Named(i) => CloneKind::Named(i.to_string().into()),
            Kind::Hidden => CloneKind::Bare,
            Kind::Export => CloneKind::Export,
        }
    }
}

impl<'tcx> CloneInfo {
    fn from_name(name: Symbol, public: bool) -> Self {
        CloneInfo { kind: Kind::Named(name), cloned: false, public, opaque: CloneOpacity::Default }
    }

    fn hidden() -> Self {
        CloneInfo {
            kind: Kind::Hidden,
            cloned: false,
            public: false,
            opaque: CloneOpacity::Default,
        }
    }

    pub(crate) fn opaque(&mut self) {
        self.opaque = CloneOpacity::Opaque;
    }

    fn qname_ident(&self, method: Ident) -> QName {
        self.kind.qname_ident(method)
    }
}

impl<'tcx> CloneMap<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, self_id: TransId, clone_level: CloneLevel) -> Self {
        let mut names = IndexMap::new();

        debug!("cloning self: {:?}", self_id);
        names.insert(CloneNode::from_trans_id(tcx, self_id), CloneInfo::hidden());

        CloneMap {
            tcx,
            self_id,
            names,
            name_counts: Default::default(),
            prelude: IndexMap::new(),
            clone_level,
            clone_graph: DiGraphMap::new(),
            last_cloned: 0,
            public: false,
            used_types: Default::default(),
        }
    }

    pub(crate) fn summary(&self) -> CloneSummary<'tcx> {
        self.names
            .iter()
            .filter_map(|(k, ci)| match &ci.kind {
                Kind::Named(_) => Some((*k, ci.clone())),
                _ => None,
            })
            .collect()
    }

    pub(crate) fn with_public_clones<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        let public = std::mem::replace(&mut self.public, true);
        let ret = f(self);
        self.public = public;
        ret
    }

    /// Internal: only meant for mutually recursive type declaration
    pub(crate) fn insert_hidden(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) {
        let node = CloneNode::new(self.tcx, (def_id, subst)).erase_regions(self.tcx);
        self.names.insert(node, CloneInfo::hidden());
    }

    #[deprecated(
        note = "Avoid using this method in favor of one of the more semantic alternatives: `value`, `accessor`, `ty`"
    )]
    pub(crate) fn insert(&mut self, key: CloneNode<'tcx>) -> &mut CloneInfo {
        let key = key.erase_regions(self.tcx).closure_hack(self.tcx);

        self.names.entry(key).or_insert_with(|| {
            if let CloneNode::Type(ty) = key && !matches!(ty.kind(), TyKind::Alias(_, _)) {
                return if let Some((did, _)) = key.did() {
                    let name = Symbol::intern(&*module_name(self.tcx, did));
                    CloneInfo::from_name(name, self.public)
                } else {
                    CloneInfo::hidden()
                };
            }

            let base = if let CloneNode::TyInv(_, inv_kind) = key {
                Symbol::intern(&*inv_module_name(self.tcx, inv_kind))
            } else {
                let did = key.did().unwrap().0;
                let base = match util::item_type(self.tcx, did) {
                    ItemType::Impl => self.tcx.item_name(self.tcx.trait_id_of_impl(did).unwrap()),
                    ItemType::Closure => Symbol::intern(&format!(
                        "closure{}",
                        self.tcx.def_path(did).data.last().unwrap().disambiguator
                    )),
                    _ => self.tcx.item_name(did),
                };
                Symbol::intern(&base.as_str().to_upper_camel_case())
            };

            let count: usize = *self.name_counts.entry(base).and_modify(|c| *c += 1).or_insert(0);
            trace!("inserting {key:?} as {base}{count}");
            CloneInfo::from_name(Symbol::intern(&format!("{base}{count}")), self.public)
        })
    }

    pub(crate) fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let name = item_name(self.tcx, def_id, Namespace::ValueNS);
        let node = CloneNode::new(self.tcx, (def_id, subst));
        self.insert(node).qname_ident(name.into())
    }

    pub(crate) fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let name = item_name(self.tcx, def_id, Namespace::TypeNS);
        let node = CloneNode::new(self.tcx, (def_id, subst));
        self.insert(node).qname_ident(name.into())
    }

    pub(crate) fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let type_id = match self.tcx.def_kind(def_id) {
            DefKind::Closure | DefKind::Struct | DefKind::Enum | DefKind::Union => def_id,
            DefKind::Variant => self.tcx.parent(def_id),
            _ => unreachable!("Not a type or constructor"),
        };
        let mut name = item_name(self.tcx, def_id, Namespace::ValueNS);
        name.capitalize();
        let node = CloneNode::new(self.tcx, (type_id, subst));
        self.insert(node).qname_ident(name.into())
    }

    /// Creates a name for a type or closure projection ie: x.field1
    /// This also includes projections from `enum` types
    ///
    /// * `def_id` - The id of the type or closure being projected
    /// * `subst` - Substitution that type is being accessed at
    /// * `variant` - The constructor being used. For closures this is always 0
    /// * `ix` - The field in that constructor being accessed.
    pub(crate) fn accessor(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
        variant: usize,
        ix: FieldIdx,
    ) -> QName {
        let tcx = self.tcx;
        let node = CloneNode::new(self.tcx, (def_id, subst));
        let clone = self.insert(node);
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

    pub(crate) fn ty_inv(&mut self, ty: Ty<'tcx>) -> QName {
        let def_id =
            self.tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = self.tcx.mk_substs(&[ty::GenericArg::from(ty)]);
        self.value(def_id, subst)
    }

    fn self_key(&self) -> CloneNode<'tcx> {
        CloneNode::from_trans_id(self.tcx, self.self_id)
    }

    fn self_did(&self) -> Option<DefId> {
        match self.self_id {
            TransId::Item(did) | TransId::TyInv(TyInvKind::Adt(did)) => Some(did),
            _ => None,
        }
    }

    fn param_env(&self, ctx: &TranslationCtx<'tcx>) -> ParamEnv<'tcx> {
        if let Some(did) = self.self_did() {
            ctx.param_env(did)
        } else {
            ParamEnv::empty()
        }
    }

    pub(crate) fn import_prelude_module(&mut self, module: PreludeModule) {
        self.import_builtin_module(module.qname());
    }

    pub(crate) fn import_builtin_module(&mut self, module: QName) {
        self.prelude.entry(module).or_insert(false);
    }

    // Update the clone graph with new entries
    fn update_graph(&mut self, ctx: &mut Why3Generator<'tcx>) {
        // Construct a maximal sharing graph for all dependencies.
        // We build edges between each (function, subst) pair, following the call graph
        // Additionally, when the substitution refers to an associated type, we construct
        // a relevant edge.
        //
        // Along the edge, we include the 'original' substitution, which we can use
        // to build the correct substitution.
        //
        let mut i = self.last_cloned;
        let param_env = self.param_env(ctx);
        while i < self.names.len() {
            let key = *self.names.get_index(i).unwrap().0;

            i += 1;
            trace!("update graph with {:?} (public={:?})", key, self.names[&key].public);

            let self_key = self.self_key();
            if key != self_key {
                self.add_graph_edge(self_key, key);
            }

            if self.names[&key].kind == Kind::Hidden {
                continue;
            }

            if let Some((did, subst)) = key.did() {
                if traits::still_specializable(self.tcx, param_env, did, subst) {
                    self.names[&key].opaque();
                }

                if self.self_did().is_some_and(|self_did| !ctx.is_transparent_from(did, self_did)) {
                    self.names[&key].opaque();
                }

                ctx.translate(did);

                if util::is_inv_internal(self.tcx, did) && self.clone_level == CloneLevel::Body {
                    let ty = subst.type_at(0);
                    let ty = ctx.try_normalize_erasing_regions(param_env, ty).unwrap_or(ty);
                    self.clone_tyinv(ctx, param_env, ty);
                }

                self.clone_laws(ctx, did, subst);
            }

            self.clone_dependencies(ctx, key);
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

        if let TransId::TyInv(self_kind) = self.self_id && self_kind == inv_kind {
            return;
        }

        ctx.translate_tyinv(inv_kind);
        self.insert(DepNode::TyInv(ty, inv_kind));
    }

    fn clone_dependencies(&mut self, ctx: &mut Why3Generator<'tcx>, key: DepNode<'tcx>) {
        let key_public = self.names[&key].public;

        if let Some((_, key_subst)) = key.did() {
            // Check the substitution for nodeendencies on closures
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
                    self.insert(node).public |= key_public;
                    self.add_graph_edge(key, node);
                }
            });
        }

        let opaque_clone = !matches!(self.clone_level, CloneLevel::Body)
            || self.names[&key].opaque == CloneOpacity::Opaque;

        trace!(
            "cloning dependencies of {:?} {:?}, len={:?}, opaque={opaque_clone}",
            self.names[&key].kind,
            key,
            ctx.dependencies(key).map(|d| d.len())
        );
        for (dep, info) in ctx.dependencies(key).iter().flat_map(|i| i.iter()) {
            if opaque_clone && !info.public && !key.is_inv() {
                continue;
            }

            trace!("adding dependency {:?} {:?}", dep, info.public);

            let orig = dep;

            let dep = self.resolve_dep(ctx, dep.subst(self.tcx, key));

            trace!("inserting dependency {:?} {:?}", key, dep);
            self.insert(dep).public |= key_public && info.public;

            // Skip reflexive edges
            if dep == key {
                continue;
            }

            let edge_set = self.add_graph_edge(key, dep);
            if let Some(sym) = refineable_symbol(ctx.tcx, *orig) {
                edge_set.insert((info.kind, sym));
            }
        }
    }

    // Adds a dependency from `user` on `prov` for the symbol `sym`.
    fn add_graph_edge(
        &mut self,
        user: DepNode<'tcx>,
        prov: DepNode<'tcx>,
    ) -> &mut IndexSet<(Kind, SymbolKind)> {
        let k1 = &self.names[&user].kind;
        let k2 = &self.names[&prov].kind;
        trace!("edge {k1:?} = {:?} --> {k2:?} = {:?}", user, prov);

        if let None = self.clone_graph.edge_weight_mut(user, prov) {
            self.clone_graph.add_edge(user, prov, IndexSet::new());
        };

        self.clone_graph.edge_weight_mut(user, prov).unwrap()
    }

    // Given an initial substitution, find out the substituted and resolved version of the dependency `dep`.
    // This will attempt to normalize traits and associated types if the substitution provides enough
    // information.
    fn resolve_dep(&self, ctx: &TranslationCtx<'tcx>, dep: DepNode<'tcx>) -> DepNode<'tcx> {
        let param_env = self.param_env(ctx);
        dep.resolve(ctx, param_env).unwrap_or(dep)
    }

    fn clone_laws(
        &mut self,
        ctx: &mut TranslationCtx<'tcx>,
        key_did: DefId,
        key_subst: SubstsRef<'tcx>,
    ) {
        let Some(item) = ctx.tcx.opt_associated_item(key_did) else { return };
        let Some(self_did) = self.self_did() else { return };

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

        if self.clone_level == CloneLevel::Stub {
            return;
        }

        let tcx = ctx.tcx;
        for law in ctx.laws(item.container_id(tcx)) {
            trace!("adding law {:?} in {:?}", *law, self.self_id);

            // No way the substitution is correct...
            let law = self.insert(DepNode::new(tcx, (*law, key_subst)));
            law.public = false;
        }
    }

    fn build_clone(&mut self, ctx: &mut Why3Generator<'tcx>, item: DepNode<'tcx>) -> Option<Decl> {
        // Types can't be cloned, but are used (for now).
        if let DepNode::Type(_) = item {
            let (def_id, _) = item.did()?;
            // check if type is not an assoc type
            if util::item_type(ctx.tcx, def_id) == ItemType::Type {
                let use_decl = self.used_types.insert(def_id).then(|| {
                    if let Some(builtin) = get_builtin(ctx.tcx, def_id) {
                        let name = QName::from_string(&builtin.as_str()).unwrap().module_qname();
                        Use { name: name, as_: None, export: false }
                    } else {
                        let name = cloneable_name(ctx, item, CloneLevel::Body);
                        Use { name: name.clone(), as_: Some(name), export: false }
                    }
                });
                return use_decl.map(Decl::UseDecl);
            }
        }

        let mut clone_subst = base_subst(ctx, self, item);
        trace!("base substs of {item:?}: {clone_subst:?}");

        let outbound: Vec<_> = self.clone_graph.neighbors_directed(item, Outgoing).collect();

        // Grab definitions from all of our dependencies
        for dep in outbound {
            let syms = &self.clone_graph[(item, dep)];
            trace!("dependency={:?} of={:?} syms={:?}", dep, item, syms);

            match dep {
                DepNode::Type(ty) => {
                    for (nm, sym) in syms.clone() {
                        let ty_name = nm.qname_ident(sym.ident());
                        let ty = backend::ty::translate_ty(ctx, self, DUMMY_SP, ty);
                        clone_subst.push(CloneSubst::Type(ty_name, ty))
                    }
                }
                _ => {
                    for (nm, sym) in syms {
                        let elem = sym.to_subst(*nm, self.names[&dep].kind);
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

        let clone_level = match (self.clone_level, self.names[&item].opaque) {
            (CloneLevel::Body, CloneOpacity::Opaque) => CloneLevel::Interface,
            (x, _) => x,
        };

        trace!(
            "emit clone node={item:?} name={:?} as={:?}",
            cloneable_name(ctx, item, clone_level),
            self.names[&item].kind.clone()
        );

        Some(Decl::Clone(DeclClone {
            name: cloneable_name(ctx, item, clone_level),
            subst: clone_subst,
            kind: self.names[&item].kind.clone().into(),
        }))
    }

    pub(crate) fn to_clones(
        mut self,
        ctx: &mut Why3Generator<'tcx>,
    ) -> (Vec<Decl>, CloneSummary<'tcx>) {
        trace!("emitting clones for {:?}", self.self_id);
        let mut decls = Vec::new();

        use petgraph::visit::Walker;

        // Update the clone graph with any new entries.
        self.update_graph(ctx);

        trace!(
            "dep_graph processed={} nodes={} edges={}",
            self.last_cloned,
            self.clone_graph.node_count(),
            self.clone_graph.edge_count()
        );

        self.last_cloned = self.names.len();

        // Broken because of closures which share a defid for the type *and* function
        // debug_assert!(!is_cyclic_directed(&self.clone_graph), "clone graph for {:?} is cyclic", self.self_id );

        let mut topo = DfsPostOrder::new(&self.clone_graph, self.self_key());
        while let Some(node) = topo.walk_next(&self.clone_graph) {
            trace!("processing node {:?}", self.names[&node].kind);

            if std::mem::replace(&mut self.names[&node].cloned, true) {
                continue;
            }

            if self.names[&node].kind == Kind::Hidden {
                continue;
            }

            let Some(decl) = self.build_clone(ctx, node) else { continue };
            decls.push(decl);
        }

        // debug_assert!(topo.finished.len() >= self.names.len(), "missed a clone in {:?}", self.self_id);

        let clones = self
            .prelude
            .iter_mut()
            .filter(|(_, v)| !(**v))
            .map(|(p, v)| {
                *v = true;
                p
            })
            .map(|q| Decl::UseDecl(Use { name: q.clone(), as_: None, export: false }))
            .chain(decls.into_iter())
            .collect();
        (clones, self.summary())
    }

    // For debugging the clone graph
    #[allow(dead_code)]
    fn to_dot(&self, ctx: &TranslationCtx<'tcx>) {
        use petgraph::dot::{Config, Dot};
        use std::io::Write;
        let path = format!("graphs/{}.dot", ctx.def_path_str(self.self_did().unwrap()));
        let mut f = std::fs::File::create(path).unwrap();
        let g = self.clone_graph.clone();
        // g.remove_node(DepNode::new(self.tcx, self.self_key()));

        write!(
            f,
            "{:?}",
            Dot::with_attr_getters(
                &g,
                &[Config::NodeNoLabel, Config::EdgeNoLabel],
                &|_, _| { String::new() },
                &|_, n| {
                    let s = match n {
                        (DepNode::Type(ty), DepNode::Type(_)) => format!("{:?}", ty),
                        (DepNode::Item(did, subst), DepNode::Item(_, _)) => {
                            format!(
                                "({}, {:?})",
                                ctx.opt_item_name(did)
                                    .map(|n| n.as_str().to_string())
                                    .unwrap_or(ctx.def_path_str(did)),
                                subst,
                            )
                        }
                        _ => panic!(),
                    };
                    format!("label = {s:?}, shape=\"rect\", style=\"rounded\"")
                },
            )
        )
        .unwrap();
    }
}

pub(crate) fn base_subst<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
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

    let param_env = names.param_env(ctx);

    let mut clone_substs = vec![];
    for (name, arg) in iter::zip(generics, substs.types()) {
        let ty = ctx.normalize_erasing_regions(param_env, arg);
        let ty = backend::ty::translate_ty(ctx, names, rustc_span::DUMMY_SP, ty);
        clone_substs.push(CloneSubst::Type(name.into(), ty));
    }
    clone_substs
}

// Which kind of module should we clone
// TODO: Unify with `CloneOpacity`
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum CloneLevel {
    Stub,
    Interface,
    Body,
}

fn cloneable_name(ctx: &TranslationCtx, dep: DepNode, clone_level: CloneLevel) -> QName {
    use util::ItemType::*;

    if let DepNode::TyInv(_, inv_kind) = dep {
        return inv_module_name(ctx.tcx, inv_kind).into();
    }

    let (def_id, _) = dep.did().unwrap();

    // TODO: Refactor.
    match util::item_type(ctx.tcx, def_id) {
        Ghost | Logic | Predicate | Impl => match clone_level {
            CloneLevel::Stub => QName {
                module: Vec::new(),
                name: format!("{}_Stub", &*module_name(ctx.tcx, def_id)).into(),
            },
            // Why do we do this? Why not use the stub here as well?
            CloneLevel::Interface => interface::interface_name(ctx, def_id).into(),
            CloneLevel::Body => module_name(ctx.tcx, def_id).into(),
        },
        Constant => match clone_level {
            CloneLevel::Body => module_name(ctx.tcx, def_id).into(),
            _ => QName {
                module: Vec::new(),
                name: format!("{}_Stub", &*module_name(ctx.tcx, def_id)).into(),
            },
        },

        Program | Closure => {
            QName { module: Vec::new(), name: interface::interface_name(ctx, def_id) }
        }
        Trait | Type | AssocTy => module_name(ctx.tcx, def_id).into(),
        Unsupported(_) => unreachable!(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum SymbolKind {
    Val(Symbol),
    Type(Symbol),
    Function(Symbol),
    Predicate(Symbol),
    Const(Symbol),
}

impl SymbolKind {
    fn sym(&self) -> Symbol {
        match self {
            SymbolKind::Val(i) => *i,
            SymbolKind::Type(i) => *i,
            SymbolKind::Function(i) => *i,
            SymbolKind::Predicate(i) => *i,
            SymbolKind::Const(i) => *i,
        }
    }

    fn ident(&self) -> Ident {
        match self {
            SymbolKind::Type(_) => ident_of_ty(self.sym()),
            _ => ident_of(self.sym()),
        }
    }

    fn to_subst(self, src: Kind, tgt: Kind) -> CloneSubst {
        let id = self.ident();
        match self {
            SymbolKind::Val(_) => CloneSubst::Val(src.qname_ident(id.clone()), tgt.qname_ident(id)),
            SymbolKind::Type(_) => CloneSubst::Type(
                src.qname_ident(id.clone()),
                why3::ty::Type::TConstructor(tgt.qname_ident(id)),
            ),
            SymbolKind::Function(_) => {
                CloneSubst::Function(src.qname_ident(id.clone()), tgt.qname_ident(id))
            }
            SymbolKind::Predicate(_) => {
                CloneSubst::Predicate(src.qname_ident(id.clone()), tgt.qname_ident(id))
            }
            SymbolKind::Const(_) => {
                // TMP
                CloneSubst::Val(src.qname_ident(id.clone()), tgt.qname_ident(id))
            }
        }
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

// Walk all the types in a substitution so we can add dependencies on them
fn walk_types<'tcx, T: TypeFoldable<TyCtxt<'tcx>>, F: FnMut(Ty<'tcx>)>(s: T, f: F) {
    s.visit_with(&mut TyVisitor { f, p: std::marker::PhantomData });
}

struct TyVisitor<'tcx, F: FnMut(Ty<'tcx>)> {
    f: F,
    p: std::marker::PhantomData<&'tcx ()>,
}

impl<'tcx, F: FnMut(Ty<'tcx>)> TypeVisitor<TyCtxt<'tcx>> for TyVisitor<'tcx, F> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        let t = match t.kind() {
            // Box<T, A> is treated as T, the A param is ignored
            TyKind::Adt(adt_def, adt_subst) if adt_def.is_box() => adt_subst.type_at(0),
            _ => t,
        };
        (self.f)(t);
        t.super_visit_with(self)
    }
}
