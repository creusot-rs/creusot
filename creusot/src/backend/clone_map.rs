use core::panic;
use std::cell::RefCell;

use crate::{
    backend::{
        Why3Generator, clone_map::elaborator::Expander, dependency::Dependency, ty::ty_to_prelude,
    },
    contracts_items::{Intrinsic, get_builtin, is_bitwise},
    ctx::*,
    naming::name,
    translation::traits::TraitResolved,
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
};
use rustc_span::Span;
use why3::{
    Exp, Ident, Name, QName, Symbol,
    coma::{Defn, Expr, Param, Prototype},
    declaration::{Attribute, Decl, Goal, Span as WSpan, TyDecl},
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

pub(crate) trait Namer<'tcx> {
    fn item(&self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Name {
        self.dependency(Dependency::Item(def_id, subst)).name()
    }

    fn item_ident(&self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Ident {
        self.dependency(Dependency::Item(def_id, subst)).ident()
    }

    fn def_ty(&self, def_id: DefId, subst: GenericArgsRef<'tcx>) -> Name {
        let ty = match self.tcx().def_kind(def_id) {
            DefKind::Enum | DefKind::Struct | DefKind::Union => {
                Ty::new_adt(self.tcx(), self.tcx().adt_def(def_id), subst)
            }
            DefKind::AssocTy => Ty::new_projection(self.tcx(), def_id, subst),
            DefKind::Closure => Ty::new_closure(self.tcx(), def_id, subst),
            DefKind::OpaqueTy => Ty::new_opaque(self.tcx(), def_id, subst),
            k => unreachable!("{k:?}"),
        };
        self.ty(ty)
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
                self.def_ty(def_id, subst);
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

    // TODO: get rid of this. It feels like it should be unnecessary
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, ty: T) -> T {
        self.tcx().normalize_erasing_regions(self.typing_env(), ty)
    }

    fn import_prelude_module(&self, module: PreMod) {
        self.dependency(Dependency::PreMod(module));
    }

    fn prelude_module_name(&self, module: PreMod) -> Box<[why3::Symbol]> {
        self.dependency(Dependency::PreMod(module));
        let name = match (module, self.bitwise_mode()) {
            (PreMod::Float32, _) => ["creusot", "float", "Float32"],
            (PreMod::Float64, _) => ["creusot", "float", "Float64"],
            (PreMod::Int, _) => ["mach", "int", "Int"],
            (PreMod::Int8, false) => ["creusot", "int", "Int8"],
            (PreMod::Int16, false) => ["creusot", "int", "Int16"],
            (PreMod::Int32, false) => ["creusot", "int", "Int32"],
            (PreMod::Int64, false) => ["creusot", "int", "Int64"],
            (PreMod::Int128, false) => ["creusot", "int", "Int128"],
            (PreMod::UInt8, false) => ["creusot", "int", "UInt8"],
            (PreMod::UInt16, false) => ["creusot", "int", "UInt16"],
            (PreMod::UInt32, false) => ["creusot", "int", "UInt32"],
            (PreMod::UInt64, false) => ["creusot", "int", "UInt64"],
            (PreMod::UInt128, false) => ["creusot", "int", "UInt128"],
            (PreMod::Int8, true) => ["creusot", "int", "Int8BW"],
            (PreMod::Int16, true) => ["creusot", "int", "Int16BW"],
            (PreMod::Int32, true) => ["creusot", "int", "Int32BW"],
            (PreMod::Int64, true) => ["creusot", "int", "Int64BW"],
            (PreMod::Int128, true) => ["creusot", "int", "Int128BW"],
            (PreMod::UInt8, true) => ["creusot", "int", "UInt8BW"],
            (PreMod::UInt16, true) => ["creusot", "int", "UInt16BW"],
            (PreMod::UInt32, true) => ["creusot", "int", "UInt32BW"],
            (PreMod::UInt64, true) => ["creusot", "int", "UInt64BW"],
            (PreMod::UInt128, true) => ["creusot", "int", "UInt128BW"],
            (PreMod::Char, _) => ["creusot", "prelude", "Char"],
            (PreMod::Opaque, _) => ["creusot", "prelude", "Opaque"],
            (PreMod::Bool, _) => ["creusot", "prelude", "Bool"],
            (PreMod::MutBor, _) => ["creusot", "prelude", "MutBorrow"],
            (PreMod::Slice, _) => {
                ["creusot", "slice", &format!("Slice{}", self.tcx().sess.target.pointer_width)]
            }
            (PreMod::Any, _) => ["creusot", "prelude", "Any"],
        };
        name.into_iter().map(Symbol::intern).collect()
    }

    fn in_pre(&self, module: PreMod, name: &str) -> QName {
        QName { module: self.prelude_module_name(module), name: Symbol::intern(name) }
            .without_search_path()
    }

    // TODO: get rid of this. `erase_and_anonymize_regions` should be the responsibility of the callers.
    // NOTE: should `Namer::ty()` be asserting with `has_erasable_regions` instead?
    fn raw_dependency(&self, dep: Dependency<'tcx>) -> &Kind;

    fn dependency(&self, dep: Dependency<'tcx>) -> &Kind {
        self.raw_dependency(dep.erase_and_anonymize_regions(self.tcx()))
    }

    fn resolve_dependency(&self, dep: Dependency<'tcx>) -> Dependency<'tcx> {
        let ctx = self.tcx();
        if let Dependency::Item(def, args) = dep {
            let (def, args) = TraitResolved::resolve_item(ctx, self.typing_env(), def, args)
                .to_opt(def, args)
                .unwrap();
            Dependency::Item(def, args)
        } else {
            dep
        }
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

    fn to_int(&self, ty: &TyKind) -> why3::QName {
        self.in_pre(ty_to_prelude(self.tcx(), ty), "t'int")
    }

    fn to_int_app(&self, ty: &TyKind, arg: why3::Exp) -> why3::Exp {
        why3::Exp::qvar(self.to_int(ty)).app([arg])
    }
}

impl<'a, 'tcx> Namer<'tcx> for CloneNames<'a, 'tcx> {
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
}

impl<'a, 'tcx> CloneNames<'a, 'tcx> {
    fn bitwise_mode(&self) -> bool {
        self.bitwise_mode
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
        self.dep_set.borrow_mut().insert(key);
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
}

pub(crate) struct Dependencies<'a, 'tcx> {
    names: CloneNames<'a, 'tcx>,

    // A hacky thing which is used to remember the dependncies we need to seed the expander with
    dep_set: RefCell<IndexSet<Dependency<'tcx>>>,
}

pub(crate) struct CloneNames<'a, 'tcx> {
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
}

impl<'a, 'tcx> CloneNames<'a, 'tcx> {
    fn new(
        ctx: &'a TranslationCtx<'tcx>,
        source_id: DefId,
        typing_env: TypingEnv<'tcx>,
        span_mode: SpanMode,
        bitwise_mode: bool,
    ) -> Self {
        CloneNames {
            ctx,
            source_id,
            typing_env,
            span_mode,
            bitwise_mode,
            names: Default::default(),
            spans: Default::default(),
            constant_setters: Setters::new(),
        }
    }
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

impl<'a, 'tcx> Dependencies<'a, 'tcx> {
    pub(crate) fn new(ctx: &'a TranslationCtx<'tcx>, self_id: DefId) -> Self {
        let bw = is_bitwise(ctx.tcx, self_id);
        let names =
            CloneNames::new(ctx, self_id, ctx.typing_env(self_id), ctx.opts.span_mode.clone(), bw);
        debug!("cloning self: {:?}", self_id);
        Dependencies { names, dep_set: Default::default() }
    }

    /// Get a name for the `Namespace` type, _without_ adding it to the list of dependencies.
    pub(crate) fn namespace_ty(&self) -> Name {
        self.names.def_ty(Intrinsic::Namespace.get(self.names.ctx), GenericArgsRef::default())
    }

    pub(crate) fn provide_deps(mut self, ctx: &Why3Generator<'tcx>) -> (Vec<Decl>, Setters) {
        trace!("emitting dependencies for {:?}", self.source_id());
        let tcx = self.tcx();
        let mut decls = Vec::new();
        let typing_env = self.typing_env();
        let source_id = self.source_id();
        let source_item = self.source_item();
        let span = tcx.def_span(source_id);

        let graph = Expander::new(
            ctx,
            &mut self.names,
            typing_env,
            self.dep_set.into_inner().into_iter(),
            span,
        );

        // Update the clone graph with any new entries.
        let (graph, mut bodies) = graph.update_graph(ctx);

        for scc in petgraph::algo::tarjan_scc(&graph).into_iter() {
            if scc.iter().any(|node| node == &source_item) {
                if scc.len() != 1 {
                    ctx.dcx().span_bug(
                        ctx.def_span(source_id),
                        format!("{} {scc:?}", ctx.def_path_str(source_id)),
                    )
                }
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
                                Dependency::Item(did, _) => matches!(
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
        let (uses, mut decls): (IndexSet<_>, Vec<_>) = decls
            .into_iter()
            .flat_map(|d| {
                if let Decl::UseDecls(u) = d { Either::Left(u) } else { Either::Right([d]) }
                    .factor_into_iter()
            })
            .partition_map(|x| x);
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
            Type(ty) => write!(f, "{ty}"),
            Item(def_id, args) => {
                write!(f, "{}{}", tcx.def_path_str(def_id), args.print_as_list())
            }
            TyInvAxiom(ty) => write!(f, "ty inv axiom {ty}"),
            ResolveAxiom(ty) => write!(f, "resolve axiom {ty}"),
            ClosureAccessor(def_id, args, _) => {
                write!(f, "closure accessor {}{}", tcx.def_path_str(def_id), args.print_as_list())
            }
            TupleField(args, field_idx) => write!(
                f,
                "tuple field ({}).{}",
                args.into_iter().map(|ty| ty.to_string()).join(", "),
                field_idx.as_u32()
            ),
            PreMod(pre_mod) => write!(f, "PreMod::{pre_mod:?}"),
            Eliminator(def_id, _args) => write!(f, "eliminator {}", tcx.def_path_str(def_id)),
            DynCast(ty1, ty2) => write!(f, "dyncast {ty1} -> {ty2}"),
            PrivateFields(def_id, _args) => {
                write!(f, "private fields {}", tcx.def_path_str(def_id))
            }
            PrivateResolve(def_id, _args) => {
                write!(f, "private resolve {}", tcx.def_path_str(def_id))
            }
            PrivateTyInv(def_id, _args) => write!(f, "private ty inv {}", tcx.def_path_str(def_id)),
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

    pub fn mk_goal(self, name: Ident, goal: Exp) -> Decl {
        if self.is_empty() {
            Decl::Goal(Goal { name, goal })
        } else {
            let prototype = Prototype {
                name,
                attrs: vec![],
                params: [Param::Cont(name::return_(), [].into(), [].into())].into(),
            };
            let body =
                self.call_setters(Expr::Assert(goal.boxed(), Expr::var(name::return_()).boxed()));
            Decl::Coma(Defn { prototype, body })
        }
    }
}
