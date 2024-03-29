#![allow(deprecated)]
use indexmap::{IndexMap, IndexSet};
use petgraph::{graphmap::DiGraphMap, visit::DfsPostOrder, EdgeDirection::Outgoing};
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
};
use rustc_middle::ty::{
    self, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable, TypeSuperVisitable,
    TypeVisitor,
};
use rustc_span::Symbol;
use rustc_target::abi::FieldIdx;

use why3::{declaration::Decl, Ident, QName};

use crate::{
    backend::{
        clone_map::{elaborator::*, expander::Expander},
        dependency::Dependency,
    },
    ctx::*,
    util::{self, item_name, module_name},
};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};

use super::{dependency::ExtendedId, ty_inv::TyInvKind, TransId, Why3Generator};

mod elaborator;
mod expander;

// Prelude modules
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, TypeVisitable, TypeFoldable)]
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

pub(crate) trait Namer<'tcx> {
    fn value(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName;

    fn ty(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName;

    fn real_ty(&mut self, ty: Ty<'tcx>) -> QName;

    fn constructor(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName;

    fn ty_inv(&mut self, ty: Ty<'tcx>) -> QName;

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
        subst: GenericArgsRef<'tcx>,
        variant: usize,
        ix: FieldIdx,
    ) -> QName;

    fn normalize(&self, ctx: &TranslationCtx<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx>;

    fn import_prelude_module(&mut self, _: PreludeModule);

    fn with_vis<F, A>(&mut self, vis: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A;
}

impl<'tcx> Namer<'tcx> for Dependencies<'tcx> {
    fn value(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let node = DepNode::new(self.tcx, (def_id, subst));

        // TODO(xavier): removing `to_snake_case` seemingly caused no issues... Investigate
        self.insert(node).qname()
    }

    fn ty(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let mut node = DepNode::new(self.tcx, (def_id, subst));

        if self.tcx.is_closure_or_coroutine(def_id) {
            node = DepNode::Type(Ty::new_closure(self.tcx, def_id, subst));
        }

        match self.tcx.def_kind(def_id) {
            DefKind::AssocTy => self.insert(node).qname(),
            _ => self.insert(node).qname(),
        }
    }

    fn real_ty(&mut self, ty: Ty<'tcx>) -> QName {
        let node = DepNode::Type(ty);
        self.insert(node).qname()
    }

    fn constructor(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let type_id = match self.tcx.def_kind(def_id) {
            DefKind::Closure | DefKind::Struct | DefKind::Enum | DefKind::Union => def_id,
            DefKind::Variant => self.tcx.parent(def_id),
            _ => unreachable!("Not a type or constructor"),
        };
        let mut name = item_name(self.tcx, def_id, Namespace::ValueNS);
        name.capitalize();
        let mut qname = self.ty(type_id, subst);
        qname.name = name.into();
        qname
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
        subst: GenericArgsRef<'tcx>,
        variant: usize,
        ix: FieldIdx,
    ) -> QName {
        let tcx = self.tcx;
        assert!(matches!(util::item_type(self.tcx, def_id), ItemType::Type | ItemType::Closure));
        let node = match util::item_type(tcx, def_id) {
            ItemType::Closure => {
                DepNode::Hacked(ExtendedId::Accessor(ix.as_u32() as u8), def_id, subst)
            }
            ItemType::Type => {
                let adt = self.tcx.adt_def(def_id);
                let field_did = adt.variants()[variant.into()].fields[ix].did;
                DepNode::new(tcx, (field_did, subst))
            }
            _ => unreachable!(),
        };

        let clone = self.insert(node);
        match util::item_type(tcx, def_id) {
            ItemType::Closure => clone.qname(),
            ItemType::Type => clone.qname(),
            _ => panic!("accessor: invalid item kind"),
        }
    }

    fn ty_inv(&mut self, ty: Ty<'tcx>) -> QName {
        let def_id =
            self.tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = self.tcx.mk_args(&[ty::GenericArg::from(ty)]);
        self.value(def_id, subst)
    }

    fn normalize(&self, ctx: &TranslationCtx<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.tcx.try_normalize_erasing_regions(self.param_env(ctx), ty).unwrap_or(ty)
    }

    fn import_prelude_module(&mut self, module: PreludeModule) {
        self.insert(DepNode::Builtin(module));
    }

    fn with_vis<F, A>(&mut self, vis: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        let public = std::mem::replace(&mut self.dep_level, vis);
        let ret = f(self);
        self.dep_level = public;
        ret
    }
}

// a clone node is expected to have a DefId
type DepNode<'tcx> = Dependency<'tcx>;
pub(super) type CloneSummary<'tcx> = IndexMap<DepNode<'tcx>, DepInfo>;

#[derive(Clone)]
pub struct Dependencies<'tcx> {
    tcx: TyCtxt<'tcx>,

    names: CloneNames<'tcx>,

    levels: IndexMap<Dependency<'tcx>, CloneLevel>,

    hidden: IndexSet<Dependency<'tcx>>,

    // TransId of the item which is cloning. Used for trait resolution
    self_id: TransId,

    // Internal state to determine whether dependencies should be public or not
    dep_level: CloneLevel,
}

#[derive(Default, Clone)]
struct NameSupply {
    name_counts: IndexMap<Symbol, usize>,
}

#[derive(Clone)]
struct CloneNames<'tcx> {
    tcx: TyCtxt<'tcx>,
    counts: NameSupply,
    names: IndexMap<DepNode<'tcx>, Kind>,
}

impl std::fmt::Debug for CloneNames<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (n, k) in &self.names {
            writeln!(f, "{n:?} -> {k:?}")?;
        }

        Ok(())
    }
}

impl<'tcx> CloneNames<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        CloneNames { tcx, counts: Default::default(), names: Default::default() }
    }
    fn insert(&mut self, key: DepNode<'tcx>) -> Kind {
        *self.names.entry(key).or_insert_with(|| match key {
            DepNode::Item(id, _) if util::item_type(self.tcx, id) == ItemType::Field => {
                let mut ty = self.tcx.parent(id);
                if util::item_type(self.tcx, ty) != ItemType::Type {
                    ty = self.tcx.parent(id);
                }
                let modl = module_name(self.tcx, ty);

                Kind::Used(modl, key.base_ident(self.tcx))
            }
            DepNode::Type(ty) if !matches!(ty.kind(), TyKind::Alias(_, _)) => {
                let kind = if let Some((did, _)) = key.did() {
                    let modl = module_name(self.tcx, did);
                    let name = Symbol::intern(&*item_name(self.tcx, did, Namespace::TypeNS));

                    Kind::Used(modl, name)
                } else {
                    Kind::Named(Symbol::intern("hidden_type_name"))
                };

                return kind;
            }
            _ => {
                let base = key.base_ident(self.tcx);

                Kind::Named(self.counts.freshen(base))
            }
        })
    }
}

impl NameSupply {
    fn freshen(&mut self, sym: Symbol) -> Symbol {
        let count: usize = *self.name_counts.entry(sym).and_modify(|c| *c += 1).or_insert(0);
        Symbol::intern(&format!("{sym}{count}"))
    }
}

#[derive(Default)]
struct DepGraph<'tcx> {
    graph: DiGraphMap<DepNode<'tcx>, CloneLevel>,
    info: IndexMap<DepNode<'tcx>, DepInfo>,
    roots: IndexSet<DepNode<'tcx>>,
    builtins: IndexSet<PreludeModule>,
}

impl<'tcx> DepGraph<'tcx> {
    fn info(&self, key: DepNode<'tcx>) -> &DepInfo {
        self.info.get(&key).unwrap_or_else(|| panic!("Could not find key {key:?}"))
    }

    fn info_mut(&mut self, key: DepNode<'tcx>) -> &mut DepInfo {
        &mut self.info[&key]
    }

    fn add_node(&mut self, key: DepNode<'tcx>, kind: Kind, level: CloneLevel) -> bool {
        let contained = self.info.contains_key(&key);
        self.info.entry(key).and_modify(|info| info.join_level(level)).or_insert(DepInfo {
            kind,
            level,
            opaque: CloneOpacity::Default,
        });
        !contained
    }

    fn add_root(&mut self, key: DepNode<'tcx>, kind: Kind, level: CloneLevel) {
        self.roots.insert(key);
        self.add_node(key, kind, level);
    }

    fn is_root(&self, key: DepNode<'tcx>) -> bool {
        self.roots.contains(&key)
    }

    // Adds a dependency from `user` on `prov` for the symbol `sym`.
    fn add_graph_edge(&mut self, user: DepNode<'tcx>, prov: DepNode<'tcx>, level: CloneLevel) {
        // trace!("edge {k1:?} = {:?} --> {k2:?} = {:?}", user, prov);

        if let None = self.graph.edge_weight_mut(user, prov) {
            self.graph.add_edge(user, prov, level);
        };
    }

    fn dependencies(
        &self,
        node: DepNode<'tcx>,
    ) -> impl Iterator<Item = (CloneLevel, DepNode<'tcx>)> + '_ {
        self.graph.edges_directed(node, Outgoing).map(|(_, n, lvl)| (*lvl, n))
    }
}

// TODO: Get rid of the enum
#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable, Hash)]
enum Kind {
    /// This symbol is locally defined
    Named(Symbol),
    /// This symbol must be acompanied by a `Use` statement in Why3
    Used(Symbol, Symbol),
}

impl Kind {
    fn ident(&self) -> Ident {
        match self {
            Kind::Named(nm) => nm.as_str().into(),
            Kind::Used(_, _) => panic!("cannot get ident of used module"),
        }
    }

    fn qname(&self) -> QName {
        match self {
            Kind::Named(nm) => nm.as_str().into(),
            Kind::Used(modl, id) => {
                QName { module: vec![modl.as_str().into()], name: id.as_str().into() }
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
enum CloneOpacity {
    Transparent,
    Opaque,
    Default,
}

/// Metadata about a specific clone including the name provided for that clone
#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct DepInfo {
    /// The highest 'visibility' this clone is visible from
    level: CloneLevel,
    /// Whether this clone is opaque (hides the body of logical functions)
    opaque: CloneOpacity,

    kind: Kind,
}

impl<'tcx> DepInfo {
    fn opaque(&mut self) {
        self.opaque = CloneOpacity::Opaque;
    }

    /// Sets level to the minimum of the current level or the provided one
    fn join_level(&mut self, level: CloneLevel) {
        self.level = self.level.min(level);
    }
}

/// Determines whether we clone only the names of symbols or if we want
/// to clone the 'whole thing' (aka contracts and logical function bodies)
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum GraphDepth {
    /// Clone the minimal amount, providing only the names (and types) of symbols
    Shallow,
    /// 'The whole she-bang', clone the entire required graph, providing the complete definitions
    /// for logical functions and the contracts for program functions.
    Deep,
}

impl<'tcx> Dependencies<'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        selfs: impl IntoIterator<Item = impl Into<TransId>>,
    ) -> Self {
        let names = CloneNames::new(tcx);
        let dep_info = IndexMap::default();
        let self_ids: Vec<_> = selfs.into_iter().map(|x| x.into()).collect();
        let self_id = self_ids[0];
        debug!("cloning self: {:?}", self_ids);
        let mut deps = Dependencies {
            tcx,
            self_id,
            names,
            levels: dep_info,
            hidden: Default::default(),
            dep_level: CloneLevel::Body,
        };

        for i in self_ids {
            let node = DepNode::from_trans_id(tcx, i);
            deps.names.names.insert(node, Kind::Named(node.base_ident(tcx)));
            deps.levels.insert(node, CloneLevel::Body);
            deps.hidden.insert(node);
        }

        deps
    }

    // Hack: for closure ty decls
    pub(crate) fn insert_hidden_type(&mut self, ty: Ty<'tcx>) {
        let node = DepNode::Type(ty);
        self.names.names.insert(node, Kind::Named(node.base_ident(self.tcx)));
        self.levels.insert(node, CloneLevel::Body);
        self.hidden.insert(node);
    }

    fn insert(&mut self, key: DepNode<'tcx>) -> Kind {
        let key = key.erase_regions(self.tcx).closure_hack(self.tcx);
        self.levels
            .entry(key)
            .and_modify(|l| {
                *l = (*l).min(self.dep_level);
            })
            .or_insert(self.dep_level);

        self.names.insert(key)
    }

    fn self_key(&self) -> DepNode<'tcx> {
        DepNode::from_trans_id(self.tcx, self.self_id)
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

    pub(crate) fn provide_deps(
        mut self,
        ctx: &mut Why3Generator<'tcx>,
        depth: GraphDepth,
    ) -> (Vec<Decl>, CloneSummary<'tcx>) {
        trace!("emitting dependencies for {:?}", self.self_id);
        let mut decls = Vec::new();

        use petgraph::visit::Walker;
        let mut roots: IndexSet<_> = self.names.names.keys().cloned().collect();

        let param_env = self.param_env(ctx);
        let self_key = self.self_key();
        let mut graph = Expander::new(&mut self.names, self_key, param_env);

        for r in &roots {
            graph.add_root(*r, self.levels[r])
        }

        // Update the clone graph with any new entries.
        let clone_graph = graph.update_graph(ctx, depth);

        {
            // Update `roots` to include any associated types which appear in the signature of another root.
            let mut i = 0;
            while i < roots.len() {
                let r = roots.get_index(i).unwrap();
                for (l, e) in clone_graph.dependencies(*r) {
                    if l == CloneLevel::Signature {
                        roots.insert(e);
                    }
                }
                i += 1
            }
        }

        let mut elab = SymbolElaborator::new(param_env);
        let mut cloned = IndexSet::new();

        for p in &clone_graph.builtins {
            self.import_prelude_module(*p);
        }

        let mut topo = DfsPostOrder::new(&clone_graph.graph, self.self_key());
        while let Some(node) = topo.walk_next(&clone_graph.graph) {
            trace!("processing node {:?}", clone_graph.info(node).kind);

            if !cloned.insert(node) {
                continue;
            }

            if self.hidden.contains(&node) {
                continue;
            }

            if !roots.contains(&node) && depth == GraphDepth::Shallow {
                continue;
            }

            let level_of_item = match (depth, clone_graph.info(node).opaque) {
                // We are requesting a deep clone of an opaque thing: stop at the contract
                (GraphDepth::Deep, CloneOpacity::Opaque) => CloneLevel::Contract,
                // Otherwise, go deep and get the body
                (GraphDepth::Deep, _) => CloneLevel::Body,
                // If we are only doing shallow dependencies, stop at the signature (no contracts)
                (GraphDepth::Shallow, _) => CloneLevel::Signature,
            };

            let decl = elab.build_clone(ctx, &mut self, node, level_of_item);
            decls.extend(decl);
        }

        // debug_assert!(topo.finished.len() >= self.names.len(), "missed a clone in {:?}", self.self_id);

        // Only return the roots (direct dependencies) of the graph as dependencies
        let summary: CloneSummary<'tcx> = roots
            .into_iter()
            .filter(|r| !self.hidden.contains(r))
            .map(|r| (r, clone_graph.info(r).clone()))
            .collect();

        let dependencies = decls;
        (dependencies, summary)
    }
}

/// Which level a clone appears at, determines its visibility in the different modules generated by Creusot
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, TyDecodable, TyEncodable, Debug, Hash)]
pub(crate) enum CloneLevel {
    /// This clone appears in a function signature or type
    Signature,
    /// This clone occurs in the contract of a function
    Contract,
    /// This clone occurs in the body of a program or logical function.
    Body,
    /// This clone is an artificial edge internally injected to 'root' dependencies
    Root,
}

// Walk all the types in a substitution so we can add dependencies on them
pub(crate) fn walk_types<'tcx, T: TypeFoldable<TyCtxt<'tcx>>, F: FnMut(Ty<'tcx>)>(s: T, f: F) {
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
