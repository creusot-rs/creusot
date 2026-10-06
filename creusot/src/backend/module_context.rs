use core::panic;
use std::{
    cell::RefCell,
    collections::{HashSet, VecDeque},
};

use crate::{
    backend::{Why3Generator, dependency::Dependency, module_context::elaborator::Expander},
    contracts_items::{Intrinsic, get_builtin, is_bitwise},
    ctx::*,
    naming::name,
    util::{erased_identity_for_item, path_of_span},
};
use creusot_args::options::SpanMode;
use elaborator::Strength;
use indexmap::IndexSet;
use itertools::{Either, Itertools};
use once_map::unsync::OnceMap;
use petgraph::prelude::DiGraphMap;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{
    GenericArgsRef, List, Ty, TyCtxt, TyKind, TypeFoldable, TypeVisitableExt, TypingEnv,
    Unnormalized,
};
use rustc_span::Span;
use rustc_type_ir::IsRigid;
use why3::{
    Exp, Ident, Name, QName, Symbol,
    coma::{Defn, Expr, Param, Prototype},
    declaration::{
        AdtDecl, Attribute, ConstructorDecl, Decl, Goal, Span as WSpan, SumRecord, TyDecl, Use,
    },
    ty::Type,
};

mod elaborator;

// Prelude modules
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, TypeVisitable, TypeFoldable)]
pub enum PreMod {
    Float32,
    Float64,
    Int,
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    Char,
    Bool,
    MutBor,
    Slice,
    Opaque,
    Any,
}

/// Implementors of this trait provide a way to give Coma names to Rust objects. They record
/// each time a type is queried so that we are able to build a set of dependencies at the end of the
/// translation.
/// It is implemented by three types:
///     - ModuleContext do not record any dependency, it simply maintain hash maps of names.
///     - module_context::dependencies adds nodes in the dependency graph,
///     - module_context::elaborator::adds nodes in the dependency graph, and edges to the current item
pub(crate) trait Namer<'tcx> {
    fn item(&self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Name {
        self.dependency(Dependency::Item(def_id, subst)).name()
    }

    fn item_ident(&self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Ident {
        self.dependency(Dependency::Item(def_id, subst)).ident()
    }

    fn ty_adt(&self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Name {
        self.ty(Ty::new_adt(self.tcx(), self.tcx().adt_def(def_id), subst))
    }

    fn ty_projection(&self, rigid: IsRigid, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Name {
        self.ty(Ty::new_projection(self.tcx(), rigid, def_id, subst))
    }

    fn ty_closure(&self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Name {
        self.ty(Ty::new_closure(self.tcx(), def_id, subst))
    }

    fn ty_opaque(&self, rigid: IsRigid, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Name {
        self.ty(Ty::new_opaque(self.tcx(), rigid, def_id, subst))
    }

    fn ty(&self, ty: Ty<'tcx>) -> Name {
        assert!(!ty.has_escaping_bound_vars());
        self.dependency(Dependency::Type(ty)).name()
    }

    /// Creates a name for a struct or closure projection ie: x.field1
    ///
    /// * `def_id` - The id of the type or closure being projected
    /// * `subst` - Substitution that type is being accessed at
    /// * `ix` - The field in that constructor being accessed.
    fn field(&self, def_id: DefId, subst: GenericArgsRef<'tcx>, ix: FieldIdx) -> Ident {
        let node = match self.tcx().def_kind(def_id) {
            DefKind::Closure => {
                self.ty_closure(def_id, subst);
                Dependency::ClosureAccessor(def_id, subst, ix.as_u32())
            }
            DefKind::Struct => {
                let fields = &self.tcx().adt_def(def_id).variants()[VariantIdx::ZERO].fields;
                Dependency::Item(fields[ix].did, subst)
            }
            DefKind::Union => unimplemented!("Field access for unions is not implemented."),
            _ => unreachable!(),
        };

        self.dependency(node).ident()
    }

    fn tuple_field(&self, args: &'tcx List<Ty<'tcx>>, idx: FieldIdx) -> Ident {
        assert!(args.len() > 1);
        self.ty(Ty::new_tup(self.tcx(), args));
        self.dependency(Dependency::TupleField(args, idx)).ident()
    }

    fn eliminator(&self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Ident {
        self.dependency(Dependency::Eliminator(def_id, subst)).ident()
    }

    fn dyn_cast(&self, source: Ty<'tcx>, target: Ty<'tcx>) -> Ident {
        self.dependency(Dependency::DynCast(source, target)).ident()
    }

    fn private_fields(&self, struct_id: DefId, subst: GenericArgsRef<'tcx>) -> Ident {
        self.dependency(Dependency::PrivateFields(struct_id, subst)).ident()
    }

    fn private_ty_inv(&self, struct_id: DefId, subst: GenericArgsRef<'tcx>) -> Ident {
        self.dependency(Dependency::PrivateTyInv(struct_id, subst)).ident()
    }

    fn private_resolve(&self, struct_id: DefId, subst: GenericArgsRef<'tcx>) -> Ident {
        self.dependency(Dependency::PrivateResolve(struct_id, subst)).ident()
    }

    /// Ideally we'd like to avoid caring about normalization in the backend,
    /// but we still need this for normalizing field types after instantiation.
    /// Also for normalizing RPITs but that seems easier to get rid of if we ever care to.
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, ty: Unnormalized<'tcx, T>) -> T {
        self.tcx().normalize_erasing_regions(self.typing_env(), ty)
    }

    fn import_prelude_module(&self, module: PreMod) {
        self.dependency(Dependency::PreMod(module));
    }

    fn prelude_module_name(&self, module: PreMod) -> Box<[why3::Symbol]> {
        self.dependency(Dependency::PreMod(module));
        let name: &[_] = match (module, self.bitwise_mode()) {
            (PreMod::Float32, _) => &["creusot", "float", "Float32"],
            (PreMod::Float64, _) => &["creusot", "float", "Float64"],
            (PreMod::Int, _) => &["int", "Int"],
            (PreMod::Int8, false) => &["creusot", "int", "Int8"],
            (PreMod::Int16, false) => &["creusot", "int", "Int16"],
            (PreMod::Int32, false) => &["creusot", "int", "Int32"],
            (PreMod::Int64, false) => &["creusot", "int", "Int64"],
            (PreMod::Int128, false) => &["creusot", "int", "Int128"],
            (PreMod::UInt8, false) => &["creusot", "int", "UInt8"],
            (PreMod::UInt16, false) => &["creusot", "int", "UInt16"],
            (PreMod::UInt32, false) => &["creusot", "int", "UInt32"],
            (PreMod::UInt64, false) => &["creusot", "int", "UInt64"],
            (PreMod::UInt128, false) => &["creusot", "int", "UInt128"],
            (PreMod::Int8, true) => &["creusot", "int", "Int8BW"],
            (PreMod::Int16, true) => &["creusot", "int", "Int16BW"],
            (PreMod::Int32, true) => &["creusot", "int", "Int32BW"],
            (PreMod::Int64, true) => &["creusot", "int", "Int64BW"],
            (PreMod::Int128, true) => &["creusot", "int", "Int128BW"],
            (PreMod::UInt8, true) => &["creusot", "int", "UInt8BW"],
            (PreMod::UInt16, true) => &["creusot", "int", "UInt16BW"],
            (PreMod::UInt32, true) => &["creusot", "int", "UInt32BW"],
            (PreMod::UInt64, true) => &["creusot", "int", "UInt64BW"],
            (PreMod::UInt128, true) => &["creusot", "int", "UInt128BW"],
            (PreMod::Char, _) => &["creusot", "prelude", "Char"],
            (PreMod::Opaque, _) => &["creusot", "prelude", "Opaque"],
            (PreMod::Bool, _) => &["creusot", "prelude", "Bool"],
            (PreMod::MutBor, _) => &["creusot", "prelude", "MutBorrow"],
            (PreMod::Slice, false) => {
                &["creusot", "slice", &format!("Slice{}", self.tcx().sess.target.pointer_width)]
            }
            (PreMod::Slice, true) => {
                &["creusot", "slice", &format!("Slice{}BW", self.tcx().sess.target.pointer_width)]
            }
            (PreMod::Any, _) => &["creusot", "prelude", "Any"],
        };
        name.into_iter().copied().map(Symbol::intern).collect()
    }

    fn in_pre(&self, module: PreMod, name: &str) -> QName {
        QName { module: self.prelude_module_name(module), name: Symbol::intern(name) }
            .without_search_path()
    }

    fn get_namespace_constructor(&self, namespace_fun: DefId) -> Ident;

    // TODO: get rid of this. `erase_and_anonymize_regions` should be the responsibility of the callers.
    // NOTE: should `Namer::ty()` be asserting with `has_erasable_regions` instead?
    fn raw_dependency(&self, dep: Dependency<'tcx>) -> &Kind;

    fn dependency(&self, dep: Dependency<'tcx>) -> &Kind {
        self.raw_dependency(dep.erase_and_anonymize_regions(self.tcx()))
    }

    fn register_constant_setter(&mut self, setter: Ident);

    fn tcx(&self) -> TyCtxt<'tcx>;

    /// The main item being translated
    fn source_id(&self) -> DefId;

    fn source_subst(&self) -> GenericArgsRef<'tcx> {
        erased_identity_for_item(self.tcx(), self.source_id())
    }

    fn source_item(&self) -> Dependency<'tcx> {
        Dependency::Item(self.source_id(), self.source_subst())
    }

    fn source_ident(&self) -> Ident {
        self.dependency(self.source_item()).ident()
    }

    fn typing_env(&self) -> TypingEnv<'tcx>;

    fn span_attr(&self, span: Span) -> Option<Attribute> {
        let ident = self.span(span)?;
        Some(Attribute::NamedSpan(ident))
    }

    fn span(&self, span: Span) -> Option<Ident>;

    fn bitwise_mode(&self) -> bool;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    /// This does not corresponds to a defined symbol
    Unnamed,
    /// This symbol is locally defined
    Named(Ident),
    /// Used, UsedBuiltin: the symbols in the last argument must be acompanied by a `use` statement in Why3
    UsedBuiltin(QName),
}

impl Kind {
    fn ident(&self) -> Ident {
        match self {
            Kind::Unnamed => panic!("Unnamed item"),
            Kind::Named(nm) => *nm,
            Kind::UsedBuiltin(_) => {
                panic!("cannot get ident of used module {self:?}")
            }
        }
    }

    fn name(&self) -> Name {
        match self {
            Kind::Unnamed => panic!("Unnamed item"),
            Kind::Named(nm) => Name::local(*nm),
            Kind::UsedBuiltin(qname) => Name::Global(qname.clone().without_search_path()),
        }
    }
}

/// The context information used for the generation of one Coma module
/// It maintain the mappings from Rust objects to Coma names
pub(crate) struct ModuleContext<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    /// The main item being translated.
    /// We need this to convert `ConstParam` into `DefId` in `tyconst_to_term_final` in `constant.rs`.
    source_id: DefId,
    // To normalize during dependency stuff (deprecated)
    typing_env: TypingEnv<'tcx>,
    // Internal state, used to determine whether we should emit spans at all
    span_mode: SpanMode,
    // Should we use the BW version of the machine integer prelude?
    bitwise_mode: bool,
    /// Tracks the name given to each dependency
    names: OnceMap<Dependency<'tcx>, Box<Kind>>,
    /// Maps spans to a unique name
    spans: OnceMap<Span, Box<Ident>>,
    /// Program functions to call to set the value of constants
    constant_setters: Setters,
    /// The set of namespaces that appears in the current function.
    ///
    /// It is reset at the start of each function.
    namespaces: OnceMap<DefId, Box<Ident>>,
}

impl<'a, 'tcx> ModuleContext<'a, 'tcx> {
    fn new(ctx: &'a TranslationCtx<'tcx>, source_id: DefId) -> Self {
        ModuleContext {
            ctx,
            source_id,
            typing_env: ctx.typing_env(source_id),
            span_mode: ctx.opts.span_mode.clone(),
            bitwise_mode: is_bitwise(ctx.tcx, source_id),
            names: Default::default(),
            spans: Default::default(),
            constant_setters: Setters::new(),
            namespaces: Default::default(),
        }
    }

    /// Get the declarations for `type namespace = ...`
    pub(crate) fn namespace_type_decls(&mut self) -> Vec<Decl> {
        let namespaces_ty = Ty::new_adt(
            self.tcx(),
            self.tcx().adt_def(Intrinsic::Namespace.get(self.ctx)),
            self.tcx().mk_args(&[]),
        );
        if self.namespaces.len() == 0 && !self.names.contains_key(&Dependency::Type(namespaces_ty))
        {
            return vec![];
        }
        let namespace_other_name = Ident::fresh_local("namespace_other");
        let other_namespaces_type =
            TyDecl::Opaque { ty_name: namespace_other_name, ty_params: [].into() };

        let namespaces = TyDecl::Adt {
            tys: [AdtDecl {
                ty_name: self.ty(namespaces_ty).to_ident(),
                ty_params: [].into(),
                sumrecord: SumRecord::Sum(
                    self.namespaces
                        .iter_mut()
                        .map(|(_, n)| ConstructorDecl {
                            name: **n,
                            fields: [Type::qconstructor(why3::QName::parse("int"))].into(),
                        })
                        .chain(std::iter::once(ConstructorDecl {
                            name: Ident::fresh_local("Other"),
                            fields: [Type::TConstructor(Name::local(namespace_other_name))].into(),
                        }))
                        .collect(),
                ),
            }]
            .into(),
        };
        vec![Decl::TyDecl(other_namespaces_type.clone()), Decl::TyDecl(namespaces.clone())]
    }
}

impl<'a, 'tcx> Namer<'tcx> for ModuleContext<'a, 'tcx> {
    fn raw_dependency(&self, key: Dependency<'tcx>) -> &Kind {
        self.names.insert(key, |_| {
            if let Some((did, _)) = key.did()
                && let Some(why3_modl) = get_builtin(self.tcx(), did)
            {
                let why3_modl =
                    why3_modl.as_str().replace("$BW$", if self.bitwise_mode { "BW" } else { "" });
                let qname = QName::parse(&why3_modl);
                return Box::new(Kind::UsedBuiltin(qname));
            }
            Box::new(key.base_ident(self.ctx).map_or(Kind::Unnamed, |base| {
                Kind::Named(Ident::fresh(crate_name(self.tcx()), base.as_str()))
            }))
        })
    }

    fn register_constant_setter(&mut self, setter: Ident) {
        self.constant_setters.0.push(setter);
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }

    fn source_id(&self) -> DefId {
        self.source_id
    }

    fn typing_env(&self) -> TypingEnv<'tcx> {
        self.typing_env
    }

    fn span(&self, span: Span) -> Option<Ident> {
        let path = path_of_span(self.tcx(), span, &self.span_mode)?;
        Some(*self.spans.insert(span, |_| {
            Box::new(Ident::fresh_local(format!(
                "s{}",
                path.file_stem().unwrap().to_str().unwrap()
            )))
        }))
    }

    fn bitwise_mode(&self) -> bool {
        self.bitwise_mode
    }

    /// Get the name of the namespace.
    ///
    /// This also:
    /// - Caches the generated name for future uses
    /// - Allow all the names defined in the current function to be later retrieved, in
    ///   order to generate the namespace type.
    fn get_namespace_constructor(&self, namespace_fun: DefId) -> Ident {
        *self.namespaces.insert(namespace_fun, |_| {
            let name = self.ctx.item_name(namespace_fun);
            Box::new(Ident::fresh_local(format!("Namespace_{name}")))
        })
    }
}

/// A wrapper of `ModuleContext`, that additionally creates dependency nodes each time a name is
/// queried.
pub(crate) struct Dependencies<'a, 'tcx> {
    names: ModuleContext<'a, 'tcx>,
    dep_graph: RefCell<DepGraphBuilder<'tcx>>,
}

/// Dependencies of a source item.
type DepGraph<'tcx> = DiGraphMap<Dependency<'tcx>, Strength>;

#[derive(Default)]
struct DepGraphBuilder<'tcx> {
    graph: DepGraph<'tcx>,
    /// Dependencies to process.
    expansion_queue: VecDeque<Dependency<'tcx>>,
    /// Set to ensure each dependency is pushed at most once in the queue.
    visited: HashSet<Dependency<'tcx>>,
}

impl<'tcx> DepGraphBuilder<'tcx> {
    /// Add a direct dependency of the source item
    fn add_node(&mut self, d: Dependency<'tcx>) {
        if self.visited.insert(d) {
            self.graph.add_node(d);
            self.expansion_queue.push_back(d);
        }
    }

    /// Add `t` as a dependency of `s`
    fn add_edge(&mut self, s: Dependency<'tcx>, strength: Strength, t: Dependency<'tcx>) {
        if let Some(old) = self.graph.add_edge(s, t, strength) {
            if old > strength {
                self.graph.add_edge(s, t, old);
            }
        } else if self.visited.insert(t) {
            self.expansion_queue.push_back(t);
        }
    }
}

impl<'a, 'tcx> Namer<'tcx> for Dependencies<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.names.tcx()
    }

    fn source_id(&self) -> DefId {
        self.names.source_id()
    }

    fn typing_env(&self) -> TypingEnv<'tcx> {
        self.names.typing_env()
    }

    fn raw_dependency(&self, key: Dependency<'tcx>) -> &Kind {
        self.dep_graph.borrow_mut().add_node(key);
        self.names.raw_dependency(key)
    }

    fn register_constant_setter(&mut self, setter: Ident) {
        self.names.register_constant_setter(setter);
    }

    fn span(&self, span: Span) -> Option<Ident> {
        self.names.span(span)
    }

    fn bitwise_mode(&self) -> bool {
        self.names.bitwise_mode()
    }

    fn get_namespace_constructor(&self, namespace_fun: DefId) -> Ident {
        self.names.get_namespace_constructor(namespace_fun)
    }
}

impl<'a, 'tcx> Dependencies<'a, 'tcx> {
    pub(crate) fn new(ctx: &'a TranslationCtx<'tcx>, self_id: DefId) -> Self {
        debug!("cloning self: {:?}", self_id);
        let names = ModuleContext::new(ctx, self_id);
        let dep_graph = RefCell::new(DepGraphBuilder::default());
        Dependencies { names, dep_graph }
    }

    /// Use this to avoid expanding the body of a recursive logic function as a dependency of its own VC.
    /// This is a hack that may need to be rethought if we add support for mutual recursion.
    pub(crate) fn visit_source(&self) {
        let source = self.names.source_item();
        self.dep_graph.borrow_mut().visited.insert(source);
    }

    pub(crate) fn translate_deps(mut self, ctx: &Why3Generator<'tcx>) -> (Vec<Decl>, Setters) {
        trace!("emitting dependencies for {:?}", self.source_id());
        let tcx = self.tcx();
        let typing_env = self.typing_env();
        let source_id = self.source_id();
        let span = tcx.def_span(source_id);

        let graph =
            Expander::new(ctx, &mut self.names, self.dep_graph.into_inner(), typing_env, span);
        let (graph, mut bodies) = graph.build_graph();

        let mut decls = self.names.namespace_type_decls();

        for scc in petgraph::algo::tarjan_scc(&graph).into_iter() {
            // Then we construct a sub-graph ignoring weak edges.
            let mut subgraph = DiGraphMap::new();

            for n in &scc {
                subgraph.add_node(*n);
            }

            for n in &scc {
                for (_, t, str) in graph.edges_directed(*n, petgraph::Direction::Outgoing) {
                    if subgraph.contains_node(t) && *str == Strength::Strong {
                        subgraph.add_edge(*n, t, ());
                    }
                }
            }

            for scc in petgraph::algo::tarjan_scc(&subgraph).into_iter() {
                if scc.len() > 1
                    && !scc.iter().all(|node| {
                        if let Some((did, _)) = node.did()
                            && (get_builtin(tcx, did).is_some() || Intrinsic::Snapshot.is(ctx, did))
                        {
                            false
                        } else {
                            match node {
                                Dependency::TupleField(..)
                                | Dependency::ClosureAccessor(..)
                                | Dependency::Eliminator(..) => true,
                                Dependency::Type(ty) => matches!(
                                    ty.kind(),
                                    TyKind::Adt(..) | TyKind::Tuple(_) | TyKind::Closure(..)
                                ),
                                &Dependency::Item(did, _) => matches!(
                                    tcx.def_kind(did),
                                    DefKind::Struct
                                        | DefKind::Enum
                                        | DefKind::Union
                                        | DefKind::Variant
                                        | DefKind::Field
                                ),
                                _ => false,
                            }
                        }
                    })
                {
                    ctx.crash_and_error(
                        ctx.def_span(scc[0].did().unwrap().0),
                        format!(
                            "encountered a cycle during translation: {}",
                            display_cycle(ctx.tcx, &scc)
                        ),
                    );
                }

                let mut bodies = scc
                    .iter()
                    .map(|node| bodies.remove(node).unwrap_or_else(|| panic!("not found {scc:?}")))
                    .collect::<Vec<_>>();

                if bodies.len() > 1 {
                    // Mutually recursive ADT
                    let tys = bodies
                        .into_iter()
                        .flatten()
                        .flat_map(|body| {
                            let Decl::TyDecl(TyDecl::Adt { tys }) = body else {
                                panic!("not an ADT decl")
                            };
                            tys
                        })
                        .collect();
                    decls.push(Decl::TyDecl(TyDecl::Adt { tys }))
                } else {
                    decls.extend(bodies.remove(0))
                }
            }
        }

        assert!(
            bodies.is_empty(),
            "unused bodies: {:?} for def {:?}",
            bodies.keys().collect::<Vec<_>>(),
            source_id
        );

        // Remove duplicates in `use` declarations, and move them at the beginning of the module
        let (mut uses, mut decls): (IndexSet<_>, Vec<_>) = decls
            .into_iter()
            .flat_map(|d| {
                if let Decl::UseDecls(u) = d { Either::Left(u) } else { Either::Right([d]) }
                    .factor_into_iter()
            })
            .partition_map(|x| x);

        // If we use the module int.Int, then we make sure we import it last, because it imports
        // notations for arithmetic operators (e.g., '+'), which may be shadowed by e.g., real.Real.
        if let Some(idx) = uses
            .get_index_of(&Use { name: self.names.prelude_module_name(PreMod::Int), export: false })
        {
            uses.move_index(idx, uses.len() - 1);
        }

        if !uses.is_empty() {
            decls.insert(0, Decl::UseDecls(uses.into_iter().collect()));
        }

        let spans: Box<[WSpan]> = self
            .names
            .spans
            .into_iter()
            .sorted_by_key(|(_, b)| **b)
            .filter_map(|(sp, name)| {
                let (path, start_line, start_column, end_line, end_column) =
                    if let Some(Attribute::Span(path, l1, c1, l2, c2)) = ctx.span_attr(sp) {
                        (path, l1, c1, l2, c2)
                    } else {
                        return None;
                    };
                Some(WSpan { name: *name, path, start_line, start_column, end_line, end_column })
            })
            .collect();

        let decls = if spans.is_empty() {
            decls
        } else {
            let mut tmp = vec![Decl::LetSpans(spans)];
            tmp.extend(decls);
            tmp
        };
        (decls, self.names.constant_setters)
    }
}

fn display_cycle<'tcx>(tcx: TyCtxt<'tcx>, scc: &[Dependency<'tcx>]) -> String {
    let mut msg = String::new();
    display_cycle_(tcx, scc, &mut msg).unwrap();
    msg
}

fn display_cycle_<'tcx>(
    tcx: TyCtxt<'tcx>,
    scc: &[Dependency<'tcx>],
    mut f: impl std::fmt::Write,
) -> std::fmt::Result {
    for (i, dep) in scc.into_iter().enumerate() {
        use Dependency::*;
        match dep {
            &Type(ty) => write!(f, "{ty}"),
            &Item(def_id, args) => {
                write!(f, "{}{}", tcx.def_path_str(def_id), args.print_as_list())
            }
            &TyInvAxiom(ty) => write!(f, "ty inv axiom {ty}"),
            &ResolveAxiom(ty) => write!(f, "resolve axiom {ty}"),
            &ClosureAccessor(def_id, args, _) => {
                write!(f, "closure accessor {}{}", tcx.def_path_str(def_id), args.print_as_list())
            }
            &TupleField(args, field_idx) => write!(
                f,
                "tuple field ({}).{}",
                args.into_iter().map(|ty| ty.to_string()).join(", "),
                field_idx.as_u32()
            ),
            &PreMod(pre_mod) => write!(f, "PreMod::{pre_mod:?}"),
            &Eliminator(def_id, _args) => write!(f, "eliminator {}", tcx.def_path_str(def_id)),
            &DynCast(ty1, ty2) => write!(f, "dyncast {ty1} -> {ty2}"),
            &PrivateFields(def_id, _args) => {
                write!(f, "private fields {}", tcx.def_path_str(def_id))
            }
            &PrivateResolve(def_id, _args) => {
                write!(f, "private resolve {}", tcx.def_path_str(def_id))
            }
            &PrivateTyInv(def_id, _args) => {
                write!(f, "private ty inv {}", tcx.def_path_str(def_id))
            }
        }?;
        f.write_str(";")?;
        if i < scc.len() - 1 {
            f.write_str(" ")?;
        }
    }
    Ok(())
}

/// Names of constant setters declared in the current module.
/// Use `call_setters` or `mk_goal` to wrap a Coma or Why3 expression with calls to these setters.
pub struct Setters(Vec<Ident>);

impl Setters {
    fn new() -> Self {
        Setters(vec![])
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn call_setters(self, mut body: why3::coma::Expr) -> why3::coma::Expr {
        for setter in self.0.into_iter() {
            body = why3::coma::Expr::var(setter).app([why3::coma::Arg::Cont(body)]);
        }
        body
    }

    pub fn mk_goal(
        self,
        name: Ident,
        args: Vec<(Ident, Type)>,
        requires: impl DoubleEndedIterator<Item = Exp>,
        ensures: Exp,
    ) -> Decl {
        if self.is_empty() {
            let goal = Exp::forall(
                args,
                requires.into_iter().rfold(ensures, |post, pre| pre.implies(post)),
            );
            Decl::Goal(Goal { name, goal })
        } else {
            let ret = Ident::fresh_local("ret");
            let params = args
                .into_iter()
                .map(|(arg, ty)| Param::Term(arg, ty))
                .chain(std::iter::once(Param::Cont(name::return_(), [].into(), [].into())))
                .collect::<Box<[_]>>();
            let prototype = Prototype { name, attrs: vec![], params };
            let body = self.call_setters(Expr::var(ret)).black_box();
            let body = requires
                .into_iter()
                .rfold(body, |body, pre| Expr::Assert(pre.boxed(), body.boxed()));
            let ret_defn = Defn {
                prototype: Prototype::new(ret, []),
                body: Expr::Assert(ensures.boxed(), Expr::var(name::return_()).black_box().boxed()),
            };
            let body = Expr::Defn(body.boxed(), false, [ret_defn].into());
            Decl::Coma(Defn { prototype, body })
        }
    }
}
