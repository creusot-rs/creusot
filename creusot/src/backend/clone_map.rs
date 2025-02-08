use crate::{
    backend::{clone_map::elaborator::Expander, dependency::Dependency, Why3Generator},
    contracts_items::{get_builtin, get_inv_function},
    ctx::*,
    options::SpanMode,
    util::{erased_identity_for_item, path_of_span},
};
use elaborator::Strength;
use indexmap::{IndexMap, IndexSet};
use petgraph::prelude::DiGraphMap;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Promoted,
    ty::{self, GenericArgsRef, Ty, TyCtxt, TyKind, TypeFoldable, TypingEnv},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::{FieldIdx, VariantIdx};
use why3::{
    declaration::{Attribute, Decl, TyDecl},
    Ident, QName,
};

mod elaborator;

// Prelude modules
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
    Intrinsic,
}

impl PreludeModule {
    pub fn qname(&self) -> Vec<Ident> {
        let qname: QName = match self {
            PreludeModule::Float32 => "prelude.prelude.Float32.".into(),
            PreludeModule::Float64 => "prelude.prelude.Float64.".into(),
            PreludeModule::Int => "prelude.prelude.Int.".into(),
            PreludeModule::Int8 => "prelude.prelude.Int8.".into(),
            PreludeModule::Int16 => "prelude.prelude.Int16.".into(),
            PreludeModule::Int32 => "prelude.prelude.Int32.".into(),
            PreludeModule::Int64 => "prelude.prelude.Int64.".into(),
            PreludeModule::Int128 => "prelude.prelude.Int128.".into(),
            PreludeModule::UInt8 => "prelude.prelude.UInt8.".into(),
            PreludeModule::UInt16 => "prelude.prelude.UInt16.".into(),
            PreludeModule::UInt32 => "prelude.prelude.UInt32.".into(),
            PreludeModule::UInt64 => "prelude.prelude.UInt64.".into(),
            PreludeModule::UInt128 => "prelude.prelude.UInt128.".into(),
            PreludeModule::Char => "prelude.prelude.Char.".into(),
            PreludeModule::Opaque => "prelude.prelude.Opaque.".into(),
            PreludeModule::Isize => "prelude.prelude.IntSize.".into(),
            PreludeModule::Usize => "prelude.prelude.UIntSize.".into(),
            PreludeModule::Bool => "prelude.prelude.Bool.".into(),
            PreludeModule::Borrow => "prelude.prelude.Borrow.".into(),
            PreludeModule::Slice => "prelude.prelude.Slice.".into(),
            PreludeModule::Intrinsic => "prelude.prelude.Intrinsic.".into(),
        };
        qname.module
    }
}

pub(crate) trait Namer<'tcx> {
    fn value(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let node = Dependency::Item(def_id, subst);
        self.insert(node).qname()
    }

    fn ty(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let ty = match self.tcx().def_kind(def_id) {
            DefKind::Enum | DefKind::Struct | DefKind::Union => {
                Ty::new_adt(self.tcx(), self.tcx().adt_def(def_id), subst)
            }
            DefKind::AssocTy => Ty::new_projection(self.tcx(), def_id, subst),
            DefKind::Closure => Ty::new_closure(self.tcx(), def_id, subst),
            DefKind::OpaqueTy => Ty::new_opaque(self.tcx(), def_id, subst),
            k => unreachable!("{k:?}"),
        };

        self.insert(Dependency::Type(ty)).qname()
    }

    fn ty_param(&mut self, ty: Ty<'tcx>) -> QName {
        assert!(matches!(ty.kind(), TyKind::Param(_)));
        self.insert(Dependency::Type(ty)).qname()
    }

    fn constructor(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        let node = Dependency::Item(def_id, subst);
        self.insert(node).qname()
    }

    fn ty_inv(&mut self, ty: Ty<'tcx>) -> QName {
        let def_id = get_inv_function(self.tcx());
        let subst = self.tcx().mk_args(&[ty::GenericArg::from(ty)]);
        self.value(def_id, subst)
    }

    /// Creates a name for a struct or closure projection ie: x.field1
    ///
    /// * `def_id` - The id of the type or closure being projected
    /// * `subst` - Substitution that type is being accessed at
    /// * `ix` - The field in that constructor being accessed.
    fn field(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>, ix: FieldIdx) -> QName {
        let node = match self.tcx().def_kind(def_id) {
            DefKind::Closure => Dependency::ClosureAccessor(def_id, subst, ix.as_u32()),
            DefKind::Struct | DefKind::Union => {
                let field_did =
                    self.tcx().adt_def(def_id).variants()[VariantIdx::ZERO].fields[ix].did;
                Dependency::Item(field_did, subst)
            }
            _ => unreachable!(),
        };

        self.insert(node).qname()
    }

    fn eliminator(&mut self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> QName {
        self.insert(Dependency::Eliminator(def_id, subst)).qname()
    }

    fn promoted(&mut self, def_id: LocalDefId, prom: Promoted) -> QName {
        self.insert(Dependency::Promoted(def_id, prom)).qname()
    }

    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, ctx: &TranslationCtx<'tcx>, ty: T) -> T;

    fn import_prelude_module(&mut self, module: PreludeModule) {
        self.insert(Dependency::Builtin(module));
    }

    fn insert(&mut self, dep: Dependency<'tcx>) -> &Kind;

    fn tcx(&self) -> TyCtxt<'tcx>;

    fn span(&mut self, span: Span) -> Option<why3::declaration::Attribute>;
}

impl<'tcx> Namer<'tcx> for CloneNames<'tcx> {
    // TODO: get rid of this. It feels like it should be unnecessary
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, _: &TranslationCtx<'tcx>, ty: T) -> T {
        self.tcx().normalize_erasing_regions(self.typing_env, ty)
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> &Kind {
        let key = key.erase_regions(self.tcx);
        CloneNames::insert(self, key)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn span(&mut self, span: Span) -> Option<why3::declaration::Attribute> {
        let path = path_of_span(self.tcx, span, &self.span_mode)?;

        let cnt = self.spans.len();
        let name = self.spans.entry(span).or_insert_with(|| {
            Symbol::intern(&format!("s{}{cnt}", path.file_stem().unwrap().to_str().unwrap()))
        });
        Some(Attribute::NamedSpan(name.to_string()))
    }
}

impl<'tcx> Namer<'tcx> for Dependencies<'tcx> {
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, ctx: &TranslationCtx<'tcx>, ty: T) -> T {
        self.tcx().normalize_erasing_regions(ctx.typing_env(self.self_id), ty)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> &Kind {
        let key = key.erase_regions(self.tcx);
        self.dep_set.insert(key);
        self.names.insert(key)
    }

    fn span(&mut self, span: Span) -> Option<Attribute> {
        self.names.span(span)
    }
}

#[derive(Clone)]
pub(crate) struct Dependencies<'tcx> {
    tcx: TyCtxt<'tcx>,

    pub names: CloneNames<'tcx>,

    // A hacky thing which is used to remember the dependncies we need to seed the expander with
    dep_set: IndexSet<Dependency<'tcx>>,

    pub(crate) self_id: DefId,
    pub(crate) self_subst: GenericArgsRef<'tcx>,
}

#[derive(Default, Clone)]
pub(crate) struct NameSupply {
    name_counts: IndexMap<Symbol, usize>,
}

#[derive(Clone)]
pub struct CloneNames<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Freshens a symbol by appending a number to the end
    counts: NameSupply,
    /// Tracks the name given to each dependency
    names: IndexMap<Dependency<'tcx>, Kind>,
    /// Maps spans to a unique name
    spans: IndexMap<Span, Symbol>,
    // To normalize during dependency stuff (deprecated)
    typing_env: TypingEnv<'tcx>,

    // Internal state, used to determine whether we should emit spans at all
    span_mode: SpanMode,
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
    fn new(tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>, span_mode: SpanMode) -> Self {
        CloneNames {
            tcx,
            counts: Default::default(),
            names: Default::default(),
            spans: Default::default(),
            typing_env,
            span_mode,
        }
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> &Kind {
        self.names.entry(key).or_insert_with(|| {
            if let Some((did, _)) = key.did()
                && let Some(why3_modl) = get_builtin(self.tcx, did)
            {
                let qname = QName::from(why3_modl.as_str());
                if qname.module.is_empty() {
                    return Kind::Named(Symbol::intern(&qname.name));
                } else {
                    return Kind::UsedBuiltin(qname);
                }
            }
            key.base_ident(self.tcx)
                .map_or(Kind::Unnamed, |base| Kind::Named(self.counts.freshen(base)))
        })
    }
}

impl NameSupply {
    pub(crate) fn freshen(&mut self, sym: Symbol) -> Symbol {
        let count: usize = *self.name_counts.entry(sym).and_modify(|c| *c += 1).or_insert(0);
        // FIXME: if we don't do use the initial ident when count == 0, then the ident clashes
        // with local variables
        /*if count == 0 {
            sym
        } else {*/
        Symbol::intern(&format!("{sym}'{count}"))
        /*}*/
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    /// This does not corresponds to a defined symbol
    Unnamed,
    /// This symbol is locally defined
    Named(Symbol),
    /// Used, UsedBuiltin: the symbols in the last argument must be acompanied by a `use` statement in Why3
    UsedBuiltin(QName),
}

impl Kind {
    fn ident(&self) -> Ident {
        match self {
            Kind::Unnamed => panic!("Unnamed item"),
            Kind::Named(nm) => nm.as_str().into(),
            Kind::UsedBuiltin(_) => {
                panic!("cannot get ident of used module {self:?}")
            }
        }
    }

    fn qname(&self) -> QName {
        match self {
            Kind::Unnamed => panic!("Unnamed item"),
            Kind::Named(nm) => nm.as_str().into(),
            Kind::UsedBuiltin(qname) => qname.clone().without_search_path(),
        }
    }
}

impl<'tcx> Dependencies<'tcx> {
    pub(crate) fn new(ctx: &TranslationCtx<'tcx>, self_id: DefId) -> Self {
        let names = CloneNames::new(ctx.tcx, ctx.typing_env(self_id), ctx.opts.span_mode.clone());
        debug!("cloning self: {:?}", self_id);
        let self_subst = erased_identity_for_item(ctx.tcx, self_id);
        let mut deps =
            Dependencies { tcx: ctx.tcx, self_id, self_subst, names, dep_set: Default::default() };

        let node = Dependency::Item(self_id, self_subst);
        deps.names.insert(node);
        deps
    }

    pub(crate) fn provide_deps(mut self, ctx: &mut Why3Generator<'tcx>) -> Vec<Decl> {
        trace!("emitting dependencies for {:?}", self.self_id);
        let mut decls = Vec::new();

        let typing_env = ctx.typing_env(self.self_id);

        let self_node = Dependency::Item(self.self_id, self.self_subst);
        let graph =
            Expander::new(&mut self.names, self_node, typing_env, self.dep_set.iter().copied());

        // Update the clone graph with any new entries.
        let (graph, mut bodies) = graph.update_graph(ctx);

        // First we find components including weak dependencies
        for scc in petgraph::algo::tarjan_scc(&graph).into_iter() {
            if scc.iter().any(|node| node == &self_node) {
                assert_eq!(scc.len(), 1);
                bodies.remove(&scc[0]);
                continue;
            }

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
                    && scc.iter().any(|node| {
                        node.did().is_none_or(|(did, _)| {
                            !matches!(
                                self.tcx.def_kind(did),
                                DefKind::Struct
                                    | DefKind::Enum
                                    | DefKind::Union
                                    | DefKind::Variant
                                    | DefKind::Field
                            ) || get_builtin(self.tcx, did).is_some()
                        })
                    })
                {
                    ctx.crash_and_error(
                        ctx.def_span(scc[0].did().unwrap().0),
                        &format!("encountered a cycle during translation: {:?}", scc),
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
            self.self_id
        );

        let spans: Vec<why3::declaration::Span> = self
            .names
            .spans
            .into_iter()
            .filter_map(|(sp, name)| {
                let (path, start_line, start_column, end_line, end_column) =
                    if let Some(Attribute::Span(path, l1, c1, l2, c2)) = ctx.span_attr(sp) {
                        (path, l1, c1, l2, c2)
                    } else {
                        return None;
                    };

                Some(why3::declaration::Span {
                    name: name.as_str().into(),
                    path,
                    start_line,
                    start_column,
                    end_line,
                    end_column,
                })
            })
            .collect();

        let dependencies = if spans.is_empty() {
            decls
        } else {
            let mut tmp = vec![Decl::LetSpans(spans)];
            tmp.extend(decls);
            tmp
        };

        dependencies
    }
}
