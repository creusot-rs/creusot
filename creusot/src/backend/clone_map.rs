use indexmap::{IndexMap, IndexSet};
use petgraph::{graphmap::DiGraphMap, visit::DfsPostOrder};
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
};
use rustc_middle::ty::{self, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable};
use rustc_span::{FileName, Span, Symbol};
use rustc_target::abi::FieldIdx;

use why3::{
    declaration::{Attribute, Decl},
    Ident, QName,
};

use crate::{
    backend::{clone_map::elaborator::Expander, dependency::Dependency},
    ctx::*,
    options::SpanMode,
    util::{self, item_name, module_name},
};
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};

use super::{dependency::ClosureSpecKind, TransId, Why3Generator};

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
    pub fn qname(&self) -> QName {
        match self {
            PreludeModule::Float32 => QName::from_string("prelude.prelude.Float32"),
            PreludeModule::Float64 => QName::from_string("prelude.prelude.Float64"),
            PreludeModule::Int => QName::from_string("prelude.prelude.Int"),
            PreludeModule::Int8 => QName::from_string("prelude.prelude.Int8"),
            PreludeModule::Int16 => QName::from_string("prelude.prelude.Int16"),
            PreludeModule::Int32 => QName::from_string("prelude.prelude.Int32"),
            PreludeModule::Int64 => QName::from_string("prelude.prelude.Int64"),
            PreludeModule::Int128 => QName::from_string("prelude.prelude.Int128"),
            PreludeModule::UInt8 => QName::from_string("prelude.prelude.UInt8"),
            PreludeModule::UInt16 => QName::from_string("prelude.prelude.UInt16"),
            PreludeModule::UInt32 => QName::from_string("prelude.prelude.UInt32"),
            PreludeModule::UInt64 => QName::from_string("prelude.prelude.UInt64"),
            PreludeModule::UInt128 => QName::from_string("prelude.prelude.UInt128"),
            PreludeModule::Char => QName::from_string("prelude.prelude.Char"),
            PreludeModule::Opaque => QName::from_string("prelude.prelude.Opaque"),
            PreludeModule::Isize => QName::from_string("prelude.prelude.IntSize"),
            PreludeModule::Usize => QName::from_string("prelude.prelude.UIntSize"),
            PreludeModule::Bool => QName::from_string("prelude.prelude.Bool"),
            PreludeModule::Borrow => QName::from_string("prelude.prelude.Borrow"),
            PreludeModule::Slice => QName::from_string("prelude.prelude.Slice"),
            PreludeModule::Intrinsic => QName::from_string("prelude.prelude.Intrinsic"),
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

        self.insert(node).qname()
    }

    fn ty_param(&mut self, ty: Ty<'tcx>) -> QName {
        assert!(matches!(ty.kind(), TyKind::Param(_)));
        self.insert(Dependency::Type(ty)).qname()
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
                Dependency::ClosureSpec(ClosureSpecKind::Accessor(ix.as_u32() as u8), def_id, subst)
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
                qname.name = Dependency::new(tcx, (def_id, subst))
                    .base_ident(tcx)
                    .unwrap()
                    .to_string()
                    .into();
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

    fn insert(&mut self, dep: Dependency<'tcx>) -> Kind;

    fn tcx(&self) -> TyCtxt<'tcx>;

    fn span(&mut self, span: Span) -> Option<why3::declaration::Attribute>;
}

impl<'tcx> Namer<'tcx> for CloneNames<'tcx> {
    // TODO: get rid of this. It feels like it should be unnecessary
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(
        &self,
        _: &TranslationCtx<'tcx>,
        ty: T,
    ) -> T {
        self.tcx().try_normalize_erasing_regions(self.param_env, ty).unwrap_or(ty)
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> Kind {
        let key = key.erase_regions(self.tcx);
        CloneNames::insert(self, key)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn span(&mut self, span: Span) -> Option<why3::declaration::Attribute> {
        if span.is_dummy() {
            return None;
        }

        let lo = self.tcx.sess.source_map().lookup_char_pos(span.lo());
        let rustc_span::FileName::Real(path) = &lo.file.name else { return None };
        match (&self.span_mode, path) {
            (SpanMode::Relative(_), rustc_span::RealFileName::Remapped { .. }) => return None,
            _ => (),
        };

        let cnt = self.spans.len();
        let name = self.spans.entry(span).or_insert_with(|| {
            let lo = self.tcx.sess.source_map().lookup_char_pos(span.lo());

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

impl<'tcx> Namer<'tcx> for Dependencies<'tcx> {
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(
        &self,
        ctx: &TranslationCtx<'tcx>,
        ty: T,
    ) -> T {
        self.tcx()
            .try_normalize_erasing_regions(Self::param_env(self.self_id, ctx), ty)
            .unwrap_or(ty)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> Kind {
        let key = key.erase_regions(self.tcx);
        self.dep_set.insert(key);
        self.names.insert(key)
    }

    fn span(&mut self, span: Span) -> Option<Attribute> {
        self.names.span(span)
    }
}

#[derive(Clone)]
pub struct Dependencies<'tcx> {
    tcx: TyCtxt<'tcx>,

    names: CloneNames<'tcx>,

    // A hacky thing which is used to remember the dependncies we need to seed the expander with
    dep_set: IndexSet<Dependency<'tcx>>,

    hidden: IndexSet<Dependency<'tcx>>,

    // TransId of the item which is cloning. Used for trait resolution
    self_id: TransId<'tcx>,
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
    // To normalize during dependency stuff (deprecated)
    param_env: ParamEnv<'tcx>,

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
    fn new(tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>, span_mode: SpanMode) -> Self {
        CloneNames {
            tcx,
            counts: Default::default(),
            names: Default::default(),
            adt_names: Default::default(),
            spans: Default::default(),
            param_env,
            span_mode,
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

                Kind::Used(modl, key.base_ident(self.tcx).unwrap())
            }
            Dependency::Type(ty) if !matches!(ty.kind(), TyKind::Alias(_, _) | TyKind::Param(_)) => {
                if let Some((did, _)) = key.did() {
                    let (modl, name) = if let Some(why3_modl) = util::get_builtin(self.tcx, did) {
                        let qname = QName::from_string(why3_modl.as_str());
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
                    Kind::Unnamed
                }
            }
            Dependency::Item(id, _) if util::item_type(self.tcx, id) == ItemType::Variant => {
                let ty = self.tcx.parent(id);
                let modl = module_name(self.tcx, ty);

                Kind::Used(modl, key.base_ident(self.tcx).unwrap())
            }
            _ => {
                if let Dependency::Item(id, _) = key
                    && let Some(why3_modl) = util::get_builtin(self.tcx, id)
                {
                    let qname = QName::from_string(why3_modl.as_str());
                    let name = qname.name.clone();
                    let modl = qname.module_qname().name;
                    return Kind::Used(Symbol::intern(&*modl), Symbol::intern(&*name));
                };

                key.base_ident(self.tcx)
                    .map_or(Kind::Unnamed, |base| Kind::Named(self.counts.freshen(base)))
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

// TODO: Get rid of the enum
#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable, Hash)]
pub enum Kind {
    /// This does not corresponds to a defined symbol
    Unnamed,
    /// This symbol is locally defined
    Named(Symbol),
    /// This symbol must be acompanied by a `Use` statement in Why3
    Used(Symbol, Symbol),
}

impl Kind {
    fn ident(&self) -> Ident {
        match self {
            Kind::Unnamed => panic!("Unnamed item"),
            Kind::Named(nm) => nm.as_str().into(),
            Kind::Used(_, _) => panic!("cannot get ident of used module {self:?}"),
        }
    }

    fn qname(&self) -> QName {
        match self {
            Kind::Unnamed => panic!("Unnamed item"),
            Kind::Named(nm) => nm.as_str().into(),
            Kind::Used(modl, id) => {
                QName { module: vec![modl.as_str().into()], name: id.as_str().into() }
            }
        }
    }
}

impl<'tcx> Dependencies<'tcx> {
    pub(crate) fn new(
        ctx: &TranslationCtx<'tcx>,
        selfs: impl IntoIterator<Item = impl Into<TransId<'tcx>>>,
    ) -> Self {
        let self_ids: Vec<_> = selfs.into_iter().map(|x| x.into()).collect();
        let self_id = self_ids[0];
        let names =
            CloneNames::new(ctx.tcx, Self::param_env(self_id, ctx), ctx.opts.span_mode.clone());
        debug!("cloning self: {:?}", self_ids);
        let mut deps = Dependencies {
            tcx: ctx.tcx,
            self_id,
            names,
            dep_set: Default::default(),
            hidden: Default::default(),
        };

        for i in self_ids {
            let node = Dependency::from_trans_id(ctx.tcx, i);
            deps.names
                .names
                .insert(node, node.base_ident(ctx.tcx).map_or(Kind::Unnamed, Kind::Named));
            deps.hidden.insert(node);
        }

        deps
    }

    // Hack: for closure ty decls
    pub(crate) fn insert_hidden_type(&mut self, ty: Ty<'tcx>) {
        let node = Dependency::Type(ty);
        self.names.names.insert(node, Kind::Named(node.base_ident(self.tcx).unwrap()));
        self.hidden.insert(node);
    }

    fn self_key(&self) -> Dependency<'tcx> {
        Dependency::from_trans_id(self.tcx, self.self_id)
    }

    fn param_env(self_id: TransId, ctx: &TranslationCtx<'tcx>) -> ParamEnv<'tcx> {
        match self_id {
            TransId::Item(did) => ctx.param_env(did),
            TransId::StructuralResolve(ty) | TransId::TyInvAxiom(ty) => ty
                .ty_adt_def()
                .map(|adt_def| ctx.param_env(adt_def.did()))
                .unwrap_or_else(|| ParamEnv::empty()),
            TransId::Hacked(_, did) => ctx.param_env(did),
        }
    }

    pub(crate) fn provide_deps(mut self, ctx: &mut Why3Generator<'tcx>) -> Vec<Decl> {
        trace!("emitting dependencies for {:?}", self.self_id);
        let mut decls = Vec::new();

        use petgraph::visit::Walker;
        let param_env = Self::param_env(self.self_id, ctx);
        let self_key = self.self_key();

        let graph = Expander::new(
            &mut self.names,
            self_key,
            param_env,
            self.tcx,
            self.dep_set.iter().copied(),
        );

        // Update the clone graph with any new entries.
        let (graph, bodies) = graph.update_graph(ctx);

        // assert!(!petgraph::algo::is_cyclic_directed(&graph));

        let mut cloned = IndexSet::new();

        // This serves as a last-resort check against mutual recursion in supported contexts
        // We already filter mutually recursive logical definitions ahead of this, but must check it again here.
        // TODO: Detect this incrementally rather than after the fact?
        let cycles = petgraph::algo::tarjan_scc(&graph);
        for cycle in cycles {
            // Types and invariants are allowed to be mutually recursive
            if cycle[0].is_type() || cycle[0].is_invariant() {
                continue;
            }
            // All definitions are allowed to be simply recursive
            if cycle.len() == 1 {
                continue;
            }

            ctx.crash_and_error(
                ctx.def_span(cycle[0].did().unwrap().0),
                &format!("encountered a cycle during translation: {:?}", cycle),
            );
        }

        for (n, k) in &self.names.names {
            if format!("{:?}", k).contains("Closure'4") {
                eprintln!("{:?} {n:?}", k);
            }
        }

        let mut topo = DfsPostOrder::new(&graph, self.self_key());
        while let Some(node) = topo.walk_next(&graph) {
            // eprintln!("Cloning node for {node:?}");
            // trace!("processing node {:?}", clone_graph.info(node).kind);

            if !cloned.insert(node) {
                continue;
            }

            if self.hidden.contains(&node) {
                continue;
            }

            let body = bodies.get(&node).unwrap_or_else(|| panic!("not found {node:?}"));

            decls.extend(body.clone());
        }

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
