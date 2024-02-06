#![allow(deprecated)]

use heck::ToSnakeCase;
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

use why3::{
    declaration::{CloneKind, Decl},
    Ident, QName,
};

use crate::{
    backend::{
        clone_map::{elaborator::*, expander::Expander},
        dependency::Dependency,
    },
    ctx::*,
    util::{self, item_name, module_name},
};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};

use super::{dependency::HackedId, ty_inv::TyInvKind, TransId, Why3Generator};

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

impl<'tcx> Namer<'tcx> for CloneMap<'tcx> {
    fn value(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let node = DepNode::new(self.tcx, (def_id, subst));
        match self.insert(node) {
            Kind::Hidden(nm) => nm.as_str().to_snake_case().into(),
            Kind::Named(nm) => nm.as_str().to_snake_case().into(),
        }
    }

    fn ty(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let mut node = DepNode::new(self.tcx, (def_id, subst));

        if self.tcx.is_closure(def_id) {
            node = DepNode::Type(Ty::new_closure(self.tcx, def_id, subst));
        }

        let name = item_name(self.tcx, def_id, Namespace::TypeNS);
        match self.tcx.def_kind(def_id) {
            DefKind::AssocTy => self.insert(node).ident().into(),
            _ => self.insert(node).qname_ident(name),
        }
    }

    fn real_ty(&mut self, ty: Ty<'tcx>) -> QName {
        let node = DepNode::Type(ty);
        self.insert(node).ident().into()
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
        let node = match util::item_type(tcx, def_id) {
            ItemType::Closure => {
                DepNode::Hacked(HackedId::Accessor(ix.as_u32() as u8), def_id, subst)
            }
            _ => DepNode::new(tcx, (def_id, subst)),
        };

        let clone = self.insert(node);
        match util::item_type(tcx, def_id) {
            ItemType::Closure => clone.ident().into(),
            ItemType::Type => {
                let variant_def = &tcx.adt_def(def_id).variants()[variant.into()];
                let variant = variant_def;
                let name: Ident = format!(
                    "{}_{}",
                    variant.name.as_str().to_ascii_lowercase(),
                    variant.fields[ix].name
                )
                .into();
                clone.qname_ident(name.into())
            }
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
        self.insert(DepNode::Buitlin(module));
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
pub(super) type CloneSummary<'tcx> = IndexMap<DepNode<'tcx>, CloneInfo>;

#[derive(Clone)]
pub struct CloneMap<'tcx> {
    tcx: TyCtxt<'tcx>,

    names: CloneNames<'tcx>,

    dep_info: IndexMap<Dependency<'tcx>, CloneLevel>,

    // TransId of the item which is cloning. Used for trait resolution
    self_id: TransId,

    // Internal state to determine whether clones should be public or not
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
        *self.names.entry(key).or_insert_with(|| {
            if let DepNode::Type(ty) = key && !matches!(ty.kind(), TyKind::Alias(_, _)) {
                let kind =  if let Some((did, _)) = key.did() {
                    let name = Symbol::intern(&*module_name(self.tcx, did));
                    Kind::Named(name)
                } else {
                    Kind::Hidden(Symbol::intern("hidden_type_name"))
                };

                return kind;
            }

            let base = key.base_ident(self.tcx);

            Kind::Named(self.counts.insert(base))
        })
    }
}

impl NameSupply {
    fn insert(&mut self, sym: Symbol) -> Symbol {
        let count: usize = *self.name_counts.entry(sym).and_modify(|c| *c += 1).or_insert(0);
        Symbol::intern(&format!("{sym}{count}"))
    }
}

#[derive(Default)]
struct DepGraph<'tcx> {
    graph: DiGraphMap<DepNode<'tcx>, (CloneLevel, ())>,
    info: IndexMap<DepNode<'tcx>, CloneInfo>,
    roots: IndexSet<DepNode<'tcx>>,
    builtins: IndexSet<PreludeModule>,
}

impl<'tcx> DepGraph<'tcx> {
    fn info(&self, key: DepNode<'tcx>) -> &CloneInfo {
        self.info.get(&key).unwrap_or_else(|| panic!("Could not find key {key:?}"))
    }

    fn info_mut(&mut self, key: DepNode<'tcx>) -> &mut CloneInfo {
        &mut self.info[&key]
    }

    fn add_node(&mut self, key: DepNode<'tcx>, kind: Kind, level: CloneLevel) -> bool {
        let contained = self.info.contains_key(&key);
        self.info.entry(key).and_modify(|info| info.join_level(level)).or_insert(CloneInfo {
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
            self.graph.add_edge(user, prov, (level, ()));
        };
    }

    fn dependencies(
        &self,
        node: DepNode<'tcx>,
    ) -> impl Iterator<Item = (CloneLevel, DepNode<'tcx>)> + '_ {
        self.graph.edges_directed(node, Outgoing).map(|(_, n, (lvl, _))| (*lvl, n))
    }
}

// TODO: Get rid of the enum
#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable, Hash)]
enum Kind {
    Named(Symbol),
    // Unclear why we need to keep `Hideen` around
    Hidden(Symbol),
}

impl Kind {
    fn ident(&self) -> Ident {
        match self {
            Kind::Named(nm) => nm.as_str().into(),
            Kind::Hidden(nm) => nm.as_str().into(),
        }
    }

    // TODO: Get rid
    fn qname_ident(&self, method: Ident) -> QName {
        let module = match &self {
            Kind::Named(name) => vec![name.to_string().into()],
            _ => Vec::new(),
        };
        QName { module, name: method }
    }
}

impl Into<CloneKind> for Kind {
    fn into(self) -> CloneKind {
        match self {
            Kind::Named(i) => CloneKind::Named(i.to_string().into()),
            Kind::Hidden(_) => CloneKind::Bare,
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
pub struct CloneInfo {
    /// The highest 'visibility' this clone is visible from
    level: CloneLevel,
    /// Whether this clone is opaque (hides the body of logical functions)
    opaque: CloneOpacity,

    kind: Kind,
}

impl<'tcx> CloneInfo {
    fn opaque(&mut self) {
        self.opaque = CloneOpacity::Opaque;
    }

    // fn qname_ident(&self, method: Ident) -> QName {
    //     self.kind.qname_ident(method)
    // }

    /// Sets level to the minimum of the current level or the provided one
    fn join_level(&mut self, level: CloneLevel) {
        self.level = self.level.min(level);
    }
}

/// Determines whether we clone only the names of symbols or if we want
/// to clone the 'whole thing' (aka contracts and logical function bodies)
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum CloneDepth {
    /// Clone the minimal amount, providing only the names (and types) of symbols
    Shallow,
    /// 'The whole she-bang', clone the entire required graph, providing the complete definitions
    /// for logical functions and the contracts for program functions.
    Deep,
}

impl<'tcx> CloneMap<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, self_id: TransId) -> Self {
        let mut names = CloneNames::new(tcx);
        let mut dep_info = IndexMap::default();

        debug!("cloning self: {:?}", self_id);
        let node = DepNode::from_trans_id(tcx, self_id);
        names.names.insert(node, Kind::Hidden(node.base_ident(tcx)));
        dep_info.insert(node, CloneLevel::Body);

        CloneMap { tcx, self_id, names, dep_info, dep_level: CloneLevel::Body }
    }

    /// Internal: only meant for mutually recursive type declaration
    pub(crate) fn insert_hidden(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) {
        let node = DepNode::new(self.tcx, (def_id, subst)).erase_regions(self.tcx);
        self.names.names.insert(node, Kind::Hidden(node.base_ident(self.tcx)));
        self.dep_info.insert(node, CloneLevel::Body);
    }

    // Hack: for closure ty decls
    pub(crate) fn insert_hidden_type(&mut self, ty: Ty<'tcx>) {
        let node = DepNode::Type(ty);
        self.names.names.insert(node, Kind::Hidden(node.base_ident(self.tcx)));
        self.dep_info.insert(node, CloneLevel::Body);
    }

    fn insert(&mut self, key: DepNode<'tcx>) -> Kind {
        let key = key.erase_regions(self.tcx).closure_hack(self.tcx);
        self.dep_info
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

    pub(crate) fn to_clones(
        mut self,
        ctx: &mut Why3Generator<'tcx>,
        depth: CloneDepth,
    ) -> (Vec<Decl>, CloneSummary<'tcx>) {
        trace!("emitting clones for {:?}", self.self_id);
        let mut decls = Vec::new();

        use petgraph::visit::Walker;
        let mut roots: IndexSet<_> = self.names.names.keys().cloned().collect();

        let param_env = self.param_env(ctx);
        let mut graph = Expander::new(&mut self.names, self.self_id, param_env);

        for r in &roots {
            graph.add_root(*r, self.dep_info[r])
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

            if matches!(clone_graph.info(node).kind, Kind::Hidden(_)) {
                continue;
            }

            if !roots.contains(&node) && depth == CloneDepth::Shallow {
                continue;
            }

            let level_of_item = match (depth, clone_graph.info(node).opaque) {
                // We are requesting a deep clone of an opaque thing: stop at the contract
                (CloneDepth::Deep, CloneOpacity::Opaque) => CloneLevel::Contract,
                // Otherwise, go deep and get the body
                (CloneDepth::Deep, _) => CloneLevel::Body,
                // If we are only doing shallow clones, stop at the signature (no contracts)
                (CloneDepth::Shallow, _) => CloneLevel::Signature,
            };

            let decl = elab.build_clone(ctx, &mut self, &clone_graph, node, level_of_item);
            decls.extend(decl);
        }

        // debug_assert!(topo.finished.len() >= self.names.len(), "missed a clone in {:?}", self.self_id);

        // Only return the roots (direct dependencies) of the graph as dependencies
        let summary: CloneSummary<'tcx> = roots
            .into_iter()
            .filter_map(|r| {
                if matches!(clone_graph.info(r).kind, Kind::Hidden(_)) {
                    None
                } else {
                    Some((r, clone_graph.info(r).clone()))
                }
            })
            .collect();

        let clones = decls;
        (clones, summary)
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
    /// This clone is an artificial edge internally injected to 'root' clones
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
