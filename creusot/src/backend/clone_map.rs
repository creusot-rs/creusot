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
use rustc_span::{FileName, Span, Symbol};
use rustc_target::abi::FieldIdx;

use why3::{
    declaration::{Attribute, Decl},
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

use super::{dependency::ExtendedId, TransId, Why3Generator};

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
    Intrinsic,
}

impl PreludeModule {
    pub fn qname(&self) -> QName {
        match self {
            PreludeModule::Float32 => QName::from_string("prelude.prelude.Float32").unwrap(),
            PreludeModule::Float64 => QName::from_string("prelude.prelude.Float64").unwrap(),
            PreludeModule::Int => QName::from_string("prelude.prelude.Int").unwrap(),
            PreludeModule::Int8 => QName::from_string("prelude.prelude.Int8").unwrap(),
            PreludeModule::Int16 => QName::from_string("prelude.prelude.Int16").unwrap(),
            PreludeModule::Int32 => QName::from_string("prelude.prelude.Int32").unwrap(),
            PreludeModule::Int64 => QName::from_string("prelude.prelude.Int64").unwrap(),
            PreludeModule::Int128 => QName::from_string("prelude.prelude.Int128").unwrap(),
            PreludeModule::UInt8 => QName::from_string("prelude.prelude.UInt8").unwrap(),
            PreludeModule::UInt16 => QName::from_string("prelude.prelude.UInt16").unwrap(),
            PreludeModule::UInt32 => QName::from_string("prelude.prelude.UInt32").unwrap(),
            PreludeModule::UInt64 => QName::from_string("prelude.prelude.UInt64").unwrap(),
            PreludeModule::UInt128 => QName::from_string("prelude.prelude.UInt128").unwrap(),
            PreludeModule::Char => QName::from_string("prelude.prelude.Char").unwrap(),
            PreludeModule::Opaque => QName::from_string("prelude.prelude.Opaque").unwrap(),
            PreludeModule::Ref => QName::from_string("Ref").unwrap(),
            PreludeModule::Seq => QName::from_string("prelude.prelude.Seq").unwrap(),
            PreludeModule::Type => QName::from_string("Type").unwrap(),
            PreludeModule::Isize => QName::from_string("prelude.prelude.IntSize").unwrap(),
            PreludeModule::Usize => QName::from_string("prelude.prelude.UIntSize").unwrap(),
            PreludeModule::Bool => QName::from_string("prelude.prelude.Bool").unwrap(),
            PreludeModule::Borrow => QName::from_string("prelude.prelude.Borrow").unwrap(),
            PreludeModule::Slice => QName::from_string("prelude.prelude.Slice").unwrap(),
            PreludeModule::Intrinsic => QName::from_string("prelude.prelude.Intrinsic").unwrap(),
        }
    }
}

pub(crate) trait Namer<'tcx> {
    fn value(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let node = Dependency::new(self.tcx(), (def_id, subst));
        self.insert(node).qname()
    }

    fn ty(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let mut node = Dependency::new(self.tcx(), (def_id, subst));

        if self.tcx().is_closure_like(def_id) {
            node = Dependency::Type(Ty::new_closure(self.tcx(), def_id, subst));
        }

        match self.tcx().def_kind(def_id) {
            DefKind::AssocTy => self.insert(node).qname(),
            _ => self.insert(node).qname(),
        }
    }

    fn constructor(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let type_id = match self.tcx().def_kind(def_id) {
            DefKind::Closure | DefKind::Struct | DefKind::Enum | DefKind::Union => def_id,
            DefKind::Variant => self.tcx().parent(def_id),
            _ => unreachable!("Not a type or constructor"),
        };
        let mut name = item_name(self.tcx(), def_id, Namespace::ValueNS);
        name.capitalize();
        let mut qname = self.ty(type_id, subst);
        qname.name = name.into();
        qname
    }

    fn ty_inv(&mut self, ty: Ty<'tcx>) -> QName {
        let def_id =
            self.tcx().get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = self.tcx().mk_args(&[ty::GenericArg::from(ty)]);
        self.value(def_id, subst)
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
        let tcx = self.tcx();
        let node = match util::item_type(tcx, def_id) {
            ItemType::Closure => {
                Dependency::Hacked(ExtendedId::Accessor(ix.as_u32() as u8), def_id, subst)
            }
            ItemType::Type => {
                let adt = tcx.adt_def(def_id);
                let field_did = adt.variants()[variant.into()].fields[ix].did;
                Dependency::new(tcx, (field_did, subst))
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

    fn eliminator(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let tcx = self.tcx();

        match tcx.def_kind(def_id) {
            DefKind::Variant => {
                let clone = self.insert(Dependency::new(tcx, (tcx.parent(def_id), subst)));

                let mut qname = clone.qname();
                // TODO(xavier): Remove this hack
                qname.name =
                    Dependency::new(tcx, (def_id, subst)).base_ident(tcx).to_string().into();
                qname
            }
            DefKind::Closure | DefKind::Struct | DefKind::Union => {
                let mut node = Dependency::new(tcx, (def_id, subst));

                if tcx.is_closure_like(def_id) {
                    node = Dependency::Type(Ty::new_closure(tcx, def_id, subst));
                }

                self.insert(node).qname()
            }
            _ => unreachable!(),
        }
    }
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(
        &self,
        ctx: &TranslationCtx<'tcx>,
        ty: T,
    ) -> T;

    fn import_prelude_module(&mut self, module: PreludeModule) {
        self.insert(Dependency::Builtin(module));
    }

    fn with_vis<F, A>(&mut self, vis: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A;

    fn insert(&mut self, dep: Dependency<'tcx>) -> Kind;

    fn tcx(&self) -> TyCtxt<'tcx>;

    fn span(&mut self, span: Span) -> Option<why3::declaration::Attribute>;
}

impl<'tcx> Namer<'tcx> for Dependencies<'tcx> {
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(
        &self,
        ctx: &TranslationCtx<'tcx>,
        ty: T,
    ) -> T {
        self.tcx().try_normalize_erasing_regions(self.param_env(ctx), ty).unwrap_or(ty)
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

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> Kind {
        let key = key.erase_regions(self.tcx).closure_hack(self.tcx);
        self.levels
            .entry(key)
            .and_modify(|l| {
                *l = (*l).min(self.dep_level);
            })
            .or_insert(self.dep_level);

        self.names.insert(key)
    }

    fn span(&mut self, span: Span) -> Option<Attribute> {
        if span.is_dummy() {
            return None;
        }
        let cnt = self.names.spans.len();
        let name = self.names.spans.entry(span).or_insert_with(|| {
            let lo = self.tcx.sess.source_map().lookup_char_pos(span.lo());
            if span.is_dummy() {
                return Symbol::intern(&format!("dummy{cnt}"));
            }

            if let FileName::Real(real_name) = &lo.file.name {
                let path = real_name.local_path_if_available();
                Symbol::intern(&format!("s{}{cnt}", path.file_stem().unwrap().to_str().unwrap()))
            } else {
                Symbol::intern(&format!("span{cnt}"))
            }
        });
        Some(Attribute::NamedSpan(name.to_string()))
    }
}

// a clone node is expected to have a DefId
pub(super) type CloneSummary<'tcx> = IndexMap<Dependency<'tcx>, DepInfo>;

#[derive(Clone)]
pub struct Dependencies<'tcx> {
    tcx: TyCtxt<'tcx>,

    names: CloneNames<'tcx>,

    levels: IndexMap<Dependency<'tcx>, CloneLevel>,

    hidden: IndexSet<Dependency<'tcx>>,

    // TransId of the item which is cloning. Used for trait resolution
    self_id: TransId<'tcx>,

    // Internal state to determine whether dependencies should be public or not
    dep_level: CloneLevel,
}

#[derive(Default, Clone)]
pub(crate) struct NameSupply {
    name_counts: IndexMap<Symbol, usize>,
}

#[derive(Clone)]
struct CloneNames<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Freshens a symbol by appending a number to the end
    counts: NameSupply,
    /// Tracks the name given to each dependency
    names: IndexMap<Dependency<'tcx>, Kind>,
    /// Identifies ADTs using only their name and not their substitutions
    /// This is allowed because ADTs are still polymorphic: we have a single
    /// module that we import even if we use multiple instantiations in Creusot.
    adt_names: IndexMap<DefId, Symbol>,
    /// Maps spans to a unique name
    spans: IndexMap<Span, Symbol>,
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
        CloneNames {
            tcx,
            counts: Default::default(),
            names: Default::default(),
            adt_names: Default::default(),
            spans: Default::default(),
        }
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> Kind {
        *self.names.entry(key).or_insert_with(|| match key {
            Dependency::Item(id, _) if util::item_type(self.tcx, id) == ItemType::Field => {
                let mut ty = self.tcx.parent(id);
                if util::item_type(self.tcx, ty) != ItemType::Type {
                    ty = self.tcx.parent(id);
                }
                let modl = module_name(self.tcx, ty);

                Kind::Used(modl, key.base_ident(self.tcx))
            }
            Dependency::Type(ty) if !matches!(ty.kind(), TyKind::Alias(_, _)) => {
                let kind = if let Some((did, _)) = key.did() {
                    let (modl, name) = if let Some(why3_modl) = util::get_builtin(self.tcx, did) {
                        let qname = QName::from_string(why3_modl.as_str()).unwrap();
                        let name = qname.name.clone();
                        let modl = qname.module_ident().unwrap();
                        (Symbol::intern(&modl), Symbol::intern(&*name))
                    } else {
                        let modl: Symbol = if util::item_type(self.tcx, did) == ItemType::Closure {
                            self.counts.freshen(Symbol::intern("Closure"))
                        } else {
                            match self.adt_names.get(&did) {
                                Some(nm) => *nm,
                                None => {
                                    let name = self.tcx.item_name(did);
                                    let fresh = self.counts.freshen(name);
                                    self.adt_names.insert(did, fresh);
                                    fresh
                                }
                            }
                        };

                        let name = Symbol::intern(&*item_name(self.tcx, did, Namespace::TypeNS));

                        (modl, name)
                    };

                    Kind::Used(modl, name)
                } else {
                    Kind::Named(Symbol::intern("hidden_type_name"))
                };

                return kind;
            }
            Dependency::Item(id, _) if util::item_type(self.tcx, id) == ItemType::Variant => {
                let ty = self.tcx.parent(id);
                let modl = module_name(self.tcx, ty);

                Kind::Used(modl, key.base_ident(self.tcx))
            }
            _ => {
                if let Dependency::Item(id, _) = key
                    && let Some(why3_modl) = util::get_builtin(self.tcx, id)
                {
                    let qname = QName::from_string(why3_modl.as_str()).unwrap();
                    let name = qname.name.clone();
                    let modl = qname.module_qname().name;
                    return Kind::Used(Symbol::intern(&*modl), Symbol::intern(&*name));
                };

                let base = key.base_ident(self.tcx);

                Kind::Named(self.counts.freshen(base))
            }
        })
    }
}

impl NameSupply {
    pub(crate) fn freshen(&mut self, sym: Symbol) -> Symbol {
        let count: usize = *self.name_counts.entry(sym).and_modify(|c| *c += 1).or_insert(0);
        Symbol::intern(&format!("{sym}'{count}"))
    }
}

#[derive(Default)]
struct DepGraph<'tcx> {
    graph: DiGraphMap<Dependency<'tcx>, CloneLevel>,
    info: IndexMap<Dependency<'tcx>, DepInfo>,
    roots: IndexSet<Dependency<'tcx>>,
    builtins: IndexSet<PreludeModule>,
}

impl<'tcx> DepGraph<'tcx> {
    fn info(&self, key: Dependency<'tcx>) -> &DepInfo {
        self.info.get(&key).unwrap_or_else(|| panic!("Could not find key {key:?}"))
    }

    fn info_mut(&mut self, key: Dependency<'tcx>) -> &mut DepInfo {
        &mut self.info[&key]
    }

    fn add_node(&mut self, key: Dependency<'tcx>, kind: Kind, level: CloneLevel) -> bool {
        let contained = self.info.contains_key(&key);
        self.info.entry(key).and_modify(|info| info.join_level(level)).or_insert(DepInfo {
            kind,
            level,
            opaque: CloneOpacity::Default,
        });
        !contained
    }

    fn add_root(&mut self, key: Dependency<'tcx>, kind: Kind, level: CloneLevel) {
        self.roots.insert(key);
        self.add_node(key, kind, level);
    }

    fn is_root(&self, key: Dependency<'tcx>) -> bool {
        self.roots.contains(&key)
    }

    // Adds a dependency from `user` on `prov` for the symbol `sym`.
    fn add_graph_edge(
        &mut self,
        user: Dependency<'tcx>,
        prov: Dependency<'tcx>,
        level: CloneLevel,
    ) {
        // trace!("edge {k1:?} = {:?} --> {k2:?} = {:?}", user, prov);

        if let None = self.graph.edge_weight_mut(user, prov) {
            self.graph.add_edge(user, prov, level);
        };
    }

    fn dependencies(
        &self,
        node: Dependency<'tcx>,
    ) -> impl Iterator<Item = (CloneLevel, Dependency<'tcx>)> + '_ {
        self.graph.edges_directed(node, Outgoing).map(|(_, n, lvl)| (*lvl, n))
    }
}

// TODO: Get rid of the enum
#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable, Hash)]
pub enum Kind {
    /// This symbol is locally defined
    Named(Symbol),
    /// This symbol must be acompanied by a `Use` statement in Why3
    Used(Symbol, Symbol),
}

impl Kind {
    fn ident(&self) -> Ident {
        match self {
            Kind::Named(nm) => nm.as_str().into(),
            Kind::Used(_, _) => panic!("cannot get ident of used module {self:?}"),
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
        selfs: impl IntoIterator<Item = impl Into<TransId<'tcx>>>,
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
            let node = Dependency::from_trans_id(tcx, i);
            deps.names.names.insert(node, Kind::Named(node.base_ident(tcx)));
            deps.levels.insert(node, CloneLevel::Body);
            deps.hidden.insert(node);
        }

        deps
    }

    // Hack: for closure ty decls
    pub(crate) fn insert_hidden_type(&mut self, ty: Ty<'tcx>) {
        let node = Dependency::Type(ty);
        self.names.names.insert(node, Kind::Named(node.base_ident(self.tcx)));
        self.levels.insert(node, CloneLevel::Body);
        self.hidden.insert(node);
    }

    fn self_key(&self) -> Dependency<'tcx> {
        Dependency::from_trans_id(self.tcx, self.self_id)
    }

    fn param_env(&self, ctx: &TranslationCtx<'tcx>) -> ParamEnv<'tcx> {
        match self.self_id {
            TransId::Item(did) => ctx.param_env(did),
            TransId::TyInv(ty) => ty
                .ty_adt_def()
                .map(|adt_def| ctx.param_env(adt_def.did()))
                .unwrap_or_else(|| ParamEnv::empty()),
            TransId::Hacked(_, did) => ctx.param_env(did),
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
        let mut graph = Expander::new(&mut self.names, self_key, param_env, self.tcx);

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

        let mut elab = SymbolElaborator::new(param_env, self.tcx);
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

        let mut spans: Vec<_> = self
            .names
            .spans
            .into_iter()
            .map(|(sp, name)| {
                let (nm, l1, c1, l2, c2) =
                    if let Some(Attribute::Span(nm, l1, c1, l2, c2)) = ctx.span_attr(sp) {
                        (nm, l1, c1, l2, c2)
                    } else {
                        ("".into(), 0, 0, 0, 0)
                    };

                Decl::LetSpan(name.as_str().into(), nm, l1, c1, l2, c2)
            })
            .collect();

        // Only return the roots (direct dependencies) of the graph as dependencies
        let summary: CloneSummary<'tcx> = roots
            .into_iter()
            .filter(|r| !self.hidden.contains(r))
            .map(|r| (r, clone_graph.info(r).clone()))
            .collect();

        spans.extend(decls);
        let dependencies = spans;
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
    fn visit_ty(&mut self, t: Ty<'tcx>) {
        let t = match t.kind() {
            // Box<T, A> is treated as T, the A param is ignored
            TyKind::Adt(adt_def, adt_subst) if adt_def.is_box() => adt_subst.type_at(0),
            _ => t,
        };
        (self.f)(t);
        t.super_visit_with(self)
    }
}
