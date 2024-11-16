use crate::{
    backend::{clone_map::elaborator::Expander, dependency::Dependency, Why3Generator},
    contracts_items::{get_builtin, get_inv_function},
    ctx::*,
    options::SpanMode,
    util::erased_identity_for_item,
};
use indexmap::{IndexMap, IndexSet};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Promoted,
    ty::{self, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable},
};
use rustc_span::{FileName, Span, Symbol};
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
            _ => unreachable!(),
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

    fn normalize<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(
        &self,
        ctx: &TranslationCtx<'tcx>,
        ty: T,
    ) -> T;

    fn import_prelude_module(&mut self, module: PreludeModule) {
        self.insert(Dependency::Builtin(module));
    }

    fn insert(&mut self, dep: Dependency<'tcx>) -> &Kind;

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
        self.tcx().normalize_erasing_regions(self.param_env, ty)
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> &Kind {
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
        self.tcx().normalize_erasing_regions(ctx.param_env(self.self_id), ty)
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
            spans: Default::default(),
            param_env,
            span_mode,
        }
    }

    fn insert(&mut self, key: Dependency<'tcx>) -> &Kind {
        self.names.entry(key).or_insert_with(|| {
            if let Some((did, _)) = key.did()
                && let Some(why3_modl) = get_builtin(self.tcx, did)
            {
                let qname = QName::from_string(why3_modl.as_str());
                let name = qname.name.clone();
                if let Some(modl) = qname.module_qname() {
                    return Kind::UsedBuiltin(modl, Symbol::intern(&*name));
                } else {
                    return Kind::Named(Symbol::intern(&*name));
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
    UsedBuiltin(QName, Symbol),
}

impl Kind {
    fn ident(&self) -> Ident {
        match self {
            Kind::Unnamed => panic!("Unnamed item"),
            Kind::Named(nm) => nm.as_str().into(),
            Kind::UsedBuiltin(_, _) => {
                panic!("cannot get ident of used module {self:?}")
            }
        }
    }

    fn qname(&self) -> QName {
        match self {
            Kind::Unnamed => panic!("Unnamed item"),
            Kind::Named(nm) => nm.as_str().into(),
            Kind::UsedBuiltin(modl, id) => {
                let mut module = modl.module.clone();
                module.push(modl.name.clone());
                QName { module, name: id.as_str().into() }
            }
        }
    }
}

impl<'tcx> Dependencies<'tcx> {
    pub(crate) fn new(ctx: &TranslationCtx<'tcx>, self_id: DefId) -> Self {
        let names = CloneNames::new(ctx.tcx, ctx.param_env(self_id), ctx.opts.span_mode.clone());
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

        let param_env = ctx.param_env(self.self_id);

        let self_node = Dependency::Item(self.self_id, self.self_subst);
        let graph =
            Expander::new(&mut self.names, self_node, param_env, self.dep_set.iter().copied());

        // Update the clone graph with any new entries.
        let (graph, mut bodies) = graph.update_graph(ctx);

        for scc in petgraph::algo::tarjan_scc(&graph).into_iter() {
            if scc.iter().any(|node| node == &self_node) {
                assert_eq!(scc.len(), 1);
                bodies.remove(&scc[0]);
                continue;
            }

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
