#![allow(deprecated)]

use heck::ToUpperCamelCase;
use indexmap::{IndexMap, IndexSet};
use petgraph::{graphmap::DiGraphMap, visit::DfsPostOrder, EdgeDirection::Outgoing};
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
};
use rustc_middle::ty::{
    self, subst::SubstsRef, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable, TypeSuperVisitable,
    TypeVisitor,
};
use rustc_span::Symbol;
use rustc_target::abi::FieldIdx;

use why3::{
    declaration::{CloneKind, CloneSubst, Decl, Use},
    Ident, QName,
};

use crate::{
    backend::{
        clone_map::{elaborator::CloneElaborator, expander::Expander},
        dependency::Dependency,
        interface,
    },
    ctx::*,
    util::{self, ident_of, ident_of_ty, inv_module_name, item_name, module_name},
};
use rustc_macros::{TyDecodable, TyEncodable};

use super::{ty_inv::TyInvKind, TransId, Why3Generator};

mod elaborator;
mod expander;

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

pub(crate) trait Namer<'tcx> {
    fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName;

    fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName;

    fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName;

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
    ) -> QName;

    fn normalize(&self, ctx: &TranslationCtx<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx>;

    fn import_prelude_module(&mut self, module: PreludeModule);

    fn import_builtin_module(&mut self, module: QName);
}

impl<'tcx> Namer<'tcx> for CloneMap<'tcx> {
    fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let name = item_name(self.tcx, def_id, Namespace::ValueNS);
        let node = CloneNode::new(self.tcx, (def_id, subst));
        self.insert(node).qname_ident(name.into())
    }

    fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let name = item_name(self.tcx, def_id, Namespace::TypeNS);
        let node = CloneNode::new(self.tcx, (def_id, subst));
        self.insert(node).qname_ident(name.into())
    }

    fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
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
    fn accessor(
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

    fn normalize(&self, ctx: &TranslationCtx<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.tcx.try_normalize_erasing_regions(self.param_env(ctx), ty).unwrap_or(ty)
    }

    fn import_prelude_module(&mut self, module: PreludeModule) {
        self.import_builtin_module(module.qname());
    }

    fn import_builtin_module(&mut self, module: QName) {
        self.prelude.entry(module).or_insert(false);
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

    // TransId of the item which is cloning. Used for trait resolution
    self_id: TransId,

    // Internal state to determine whether clones should be public or not
    dep_level: CloneLevel,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable, Hash)]
enum Kind {
    Named(Symbol),
    Hidden,
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

impl Into<CloneKind> for Kind {
    fn into(self) -> CloneKind {
        match self {
            Kind::Named(i) => CloneKind::Named(i.to_string().into()),
            Kind::Hidden => CloneKind::Bare,
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
    /// The name of the clone, with is effectively an `Option<String>`
    kind: Kind,
    /// The highest 'visibility' this clone is visible from
    level: CloneLevel,
    /// Whether this clone is opaque (hides the body of logical functions)
    opaque: CloneOpacity,
}

impl<'tcx> CloneInfo {
    fn from_name(name: Symbol, level: CloneLevel) -> Self {
        CloneInfo { kind: Kind::Named(name), level, opaque: CloneOpacity::Default }
    }

    fn hidden() -> Self {
        CloneInfo { kind: Kind::Hidden, level: CloneLevel::Body, opaque: CloneOpacity::Default }
    }

    fn opaque(&mut self) {
        self.opaque = CloneOpacity::Opaque;
    }

    fn qname_ident(&self, method: Ident) -> QName {
        self.kind.qname_ident(method)
    }

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
        let mut names = IndexMap::new();

        debug!("cloning self: {:?}", self_id);
        names.insert(CloneNode::from_trans_id(tcx, self_id), CloneInfo::hidden());

        CloneMap {
            tcx,
            self_id,
            names,
            name_counts: Default::default(),
            prelude: IndexMap::new(),
            dep_level: CloneLevel::Body,
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

    pub(crate) fn with_vis<F, A>(&mut self, vis: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        let public = std::mem::replace(&mut self.dep_level, vis);
        let ret = f(self);
        self.dep_level = public;
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
                    CloneInfo::from_name(name, self.dep_level)
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
            CloneInfo::from_name(Symbol::intern(&format!("{base}{count}")), self.dep_level)
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

    pub(crate) fn to_clones(
        mut self,
        ctx: &mut Why3Generator<'tcx>,
        depth: CloneDepth,
    ) -> (Vec<Decl>, CloneSummary<'tcx>) {
        trace!("emitting clones for {:?}", self.self_id);
        let mut decls = Vec::new();

        use petgraph::visit::Walker;
        let mut roots: IndexSet<_> = self.names.keys().cloned().collect();

        let mut graph = Expander::new(self);
        // Update the clone graph with any new entries.
        graph.update_graph(ctx, depth);
        // HACK, Temporary
        self = graph.clone_map;
        let clone_graph = graph.clone_graph;

        let mut elab = CloneElaborator::new(self.param_env(ctx));

        let mut i = 0;

        // The `roots` are the clones which were explicitly requested by the user, but we must extend those to include any associated types which
        // may appear in the signature of another root clone.
        while i < roots.len() {
            let r = roots.get_index(i).unwrap();
            for (_, e, (l, _)) in clone_graph.edges_directed(*r, Outgoing) {
                if *l == CloneLevel::Signature {
                    roots.insert(e);
                }
            }
            i += 1
        }

        let mut cloned = IndexSet::new();

        let mut topo = DfsPostOrder::new(&clone_graph, self.self_key());
        while let Some(node) = topo.walk_next(&clone_graph) {
            trace!("processing node {:?}", self.names[&node].kind);

            if !cloned.insert(node) {
                continue;
            }

            if self.names[&node].kind == Kind::Hidden {
                continue;
            }

            if !roots.contains(&node) && depth == CloneDepth::Shallow {
                continue;
            }

            let Some(decl) = elab.build_clone(ctx, &mut self, &clone_graph, node, depth) else { continue };
            decls.push(decl);
        }

        // debug_assert!(topo.finished.len() >= self.names.len(), "missed a clone in {:?}", self.self_id);

        let mut summary = self.summary();
        // Only return the roots (direct dependencies) of the graph as dependencies
        summary.retain(|k, _| roots.contains(k));

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

fn cloneable_name(ctx: &TranslationCtx, dep: DepNode, clone_level: CloneLevel) -> QName {
    use util::ItemType::*;

    if let DepNode::TyInv(_, inv_kind) = dep {
        return inv_module_name(ctx.tcx, inv_kind).into();
    }

    let (def_id, _) = dep.did().unwrap();

    // TODO: Refactor.
    match util::item_type(ctx.tcx, def_id) {
        Ghost | Logic | Predicate | Impl => match clone_level {
            CloneLevel::Signature => QName {
                module: Vec::new(),
                name: format!("{}_Stub", &*module_name(ctx.tcx, def_id)).into(),
            },
            // Why do we do this? Why not use the stub here as well?
            CloneLevel::Contract => interface::interface_name(ctx, def_id).into(),
            CloneLevel::Body | CloneLevel::Root => module_name(ctx.tcx, def_id).into(),
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

type DepGraph<'tcx> = DiGraphMap<DepNode<'tcx>, (CloneLevel, IndexSet<(Kind, SymbolKind)>)>;
