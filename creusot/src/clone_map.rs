use std::ops::ControlFlow;

use indexmap::IndexMap;

use petgraph::graphmap::DiGraphMap;
use petgraph::EdgeDirection::Incoming;
use why3::declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use};
use why3::{Ident, QName};

use heck::CamelCase;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    self,
    fold::TypeVisitor,
    subst::{InternalSubsts, Subst, SubstsRef},
    ProjectionTy, Ty, TyCtxt, TyKind,
};
use rustc_span::Symbol;

use crate::ctx::{self, *};
use crate::translation::{interface, traits};
use crate::util::{self, ident_of, ident_of_ty, item_name};

// Prelude modules
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PreludeModule {
    Int,
    Int8,
    Int16,
    Int32,
    Int64,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Char,
    Single,
    Double,
    Prelude,
    Ref,
    Type,
}

impl PreludeModule {
    fn qname(&self) -> QName {
        match self {
            PreludeModule::Int => QName::from_string("mach.int.Int").unwrap(),
            PreludeModule::Int8 => QName::from_string("prelude.Int8").unwrap(),
            PreludeModule::Int16 => QName::from_string("prelude.Int16").unwrap(),
            PreludeModule::Int32 => QName::from_string("mach.int.Int32").unwrap(),
            PreludeModule::Int64 => QName::from_string("mach.int.Int64").unwrap(),
            PreludeModule::UInt8 => QName::from_string("prelude.UInt8").unwrap(),
            PreludeModule::UInt16 => QName::from_string("prelude.UInt16").unwrap(),
            PreludeModule::UInt32 => QName::from_string("mach.int.UInt32").unwrap(),
            PreludeModule::UInt64 => QName::from_string("mach.int.UInt64").unwrap(),
            PreludeModule::Char => QName::from_string("string.Char").unwrap(),
            PreludeModule::Single => QName::from_string("floating_point.Single").unwrap(),
            PreludeModule::Double => QName::from_string("floating_point.Double").unwrap(),
            PreludeModule::Prelude => QName::from_string("prelude.Prelude").unwrap(),
            PreludeModule::Ref => QName::from_string("Ref").unwrap(),
            PreludeModule::Type => QName::from_string("Type").unwrap(),
        }
    }
}

type CloneNode<'tcx> = (DefId, SubstsRef<'tcx>);
pub type CloneSummary<'tcx> = IndexMap<(DefId, SubstsRef<'tcx>), CloneInfo<'tcx>>;

#[derive(Clone)]
pub struct CloneMap<'tcx> {
    tcx: TyCtxt<'tcx>,
    prelude: IndexMap<QName, bool>,
    pub names: IndexMap<CloneNode<'tcx>, CloneInfo<'tcx>>,

    // Track how many instances of a name already exist
    name_counts: IndexMap<Symbol, usize>,

    // Whether we want to be using the 'full' version of a definition.
    // When this is true we will clone the body of a logic function, however
    // we *always* clone the interface of a program definition.
    // This matches the notion of 'public' clones
    pub use_full_clones: bool,

    // DefId of the item which is cloning. Used for trait resolution
    self_id: DefId,
    // Graph which is used to calculate the full clone set
    clone_graph: DiGraphMap<CloneNode<'tcx>, Option<(DefId, SubstsRef<'tcx>)>>,
    // Index of the last cloned entry
    last_cloned: usize,

    // Internal state to determine whether clones should be public or not
    public: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
enum Kind {
    Named(Symbol),
    Hidden,
    Export,
    // Use,
}

use rustc_macros::{TyDecodable, TyEncodable};

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct CloneInfo<'tcx> {
    kind: Kind,
    additional_deps: Vec<(Symbol, (DefId, SubstsRef<'tcx>))>,
    cloned: bool,
    public: bool,
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

impl CloneInfo<'tcx> {
    fn from_name(name: Symbol, public: bool) -> Self {
        CloneInfo { kind: Kind::Named(name), additional_deps: Vec::new(), cloned: false, public }
    }

    fn hidden() -> Self {
        CloneInfo { kind: Kind::Hidden, additional_deps: Vec::new(), cloned: false, public: false }
    }

    pub fn mk_export(&mut self) {
        self.kind = Kind::Export;
    }

    pub fn add_dep(&mut self, tcx: TyCtxt<'tcx>, name: Symbol, mut dep: (DefId, SubstsRef<'tcx>)) {
        dep.1 = tcx.erase_regions(dep.1);
        self.additional_deps.push((name, dep));
    }

    // TODO: When traits stop holding all functions we can remove the last two arguments
    pub fn qname(&self, tcx: TyCtxt, def_id: DefId) -> QName {
        self.qname_raw(item_name(tcx, def_id))
    }

    pub fn qname_sym(&self, sym: rustc_span::symbol::Symbol) -> QName {
        self.qname_raw(sym.to_string().into())
    }

    fn qname_raw(&self, method: Ident) -> QName {
        let module = match &self.kind {
            Kind::Named(name) => vec![name.to_string().into()],
            _ => Vec::new(),
        };
        QName { module, name: method }
    }
}

impl<'tcx> CloneMap<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, self_id: DefId, use_full_clones: bool) -> Self {
        let names = IndexMap::new();
        CloneMap {
            tcx,
            self_id,
            names,
            name_counts: Default::default(),
            prelude: IndexMap::new(),
            use_full_clones,
            clone_graph: DiGraphMap::new(),
            last_cloned: 0,
            public: false,
        }
    }

    pub fn summary(&self) -> CloneSummary<'tcx> {
        self.names
            .iter()
            .filter_map(|(k, ci)| match &ci.kind {
                Kind::Named(_) => Some((*k, ci.clone())),
                _ => None,
            })
            .collect()
    }

    pub fn with_public_clones<F, A>(&mut self, mut f: F) -> A
    where
        F: FnMut(&mut Self) -> A,
    {
        let public = std::mem::replace(&mut self.public, true);
        let ret = f(self);
        self.public = public;
        ret
    }

    pub fn insert(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> &mut CloneInfo<'tcx> {
        let subst = self.tcx.erase_regions(subst);

        self.names.entry((def_id, subst)).or_insert_with(|| {
            debug!("inserting {:?} {:?}", def_id, subst);
            let base_sym = match util::item_type(self.tcx, def_id) {
                ItemType::Impl => self.tcx.item_name(self.tcx.trait_id_of_impl(def_id).unwrap()),
                _ => self.tcx.item_name(def_id),
            };

            let base = Symbol::intern(&base_sym.as_str().to_camel_case());
            let count: usize = *self.name_counts.entry(base).and_modify(|c| *c += 1).or_insert(0);

            let info =
                CloneInfo::from_name(Symbol::intern(&format!("{}{}", base, count)), self.public);
            info
        })
    }

    pub fn clone_self(&mut self, self_id: DefId) {
        let subst = InternalSubsts::identity_for_item(self.tcx, self_id);
        let subst = self.tcx.erase_regions(subst);

        debug!("cloning self: {:?}", (self_id, subst));
        self.names.insert((self_id, subst), CloneInfo::hidden());
    }

    pub fn import_prelude_module(&mut self, module: PreludeModule) {
        self.prelude.entry(module.qname()).or_insert(false);
    }

    pub fn import_builtin_module(&mut self, module: QName) {
        self.prelude.entry(module).or_insert(false);
    }

    pub fn keys(&self) -> impl Iterator<Item = &CloneNode<'tcx>> {
        self.names.keys()
    }

    pub fn clear_graph(&mut self) {
        for (_, b) in self.prelude.iter_mut() {
            *b = false;
        }

        for ci in self.names.values_mut() {
            ci.cloned = false;
        }
        self.last_cloned = 0;
        self.clone_graph = DiGraphMap::new();
    }

    // Update the clone graph with new entries
    fn update_graph(&mut self, ctx: &mut ctx::TranslationCtx<'_, 'tcx>) {
        // Construct a maximal sharing graph for all dependencies.
        // We build edges between each (function, subst) pair, following the call graph
        // Additionally, when the substitution refers to an associated type, we construct
        // a relevant edge.
        //
        // Along the edge, we include the 'original' substitution, which we can use
        // to build the correct substitution.
        //
        let mut i = self.last_cloned;

        while i < self.names.len() {
            let key = *self.names.get_index(i).unwrap().0;

            i += 1;
            trace!("{:?} is public={:?}", key, self.names[&key].public);

            if self.names[&key].kind == Kind::Hidden {
                continue;
            }

            self.clone_graph.add_node(key);
            ctx.translate(key.0);

            debug!("{:?} has {:?} dependencies", key, ctx.dependencies(key.0).map(|d| d.len()));
            self.clone_laws(ctx, key);
            self.clone_additional_deps(key);
            self.clone_dependencies(ctx, key);
        }
    }

    fn clone_dependencies(
        &mut self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        key: (DefId, SubstsRef<'tcx>),
    ) {
        for (dep, info) in ctx.dependencies(key.0).iter().flat_map(|i| i.iter()) {
            // TODO: This only works because we use a completely separate set of clones for
            // function interfaces and bodies. It should be refactored to be less error prone.
            if !self.use_full_clones && !info.public {
                continue;
            }
            trace!("adding dependency {:?} {:?}", dep, info.public);

            let orig = dep;
            let dep = (dep.0, dep.1.subst(self.tcx, key.1));

            let param_env = ctx.tcx.param_env(self.self_id);
            let dep = traits::resolve_opt(ctx.tcx, param_env, dep.0, dep.1).unwrap_or(dep);

            self.insert(dep.0, dep.1);

            // Skip reflexive edges
            if dep == key {
                continue;
            }

            trace!("{:?} -> {:?}", dep, key);
            self.clone_graph.add_edge(dep, key, Some(*orig));
        }
    }

    fn clone_additional_deps(&mut self, key: (DefId, SubstsRef<'tcx>)) {
        let additional_deps = self.names[&key].additional_deps.clone();
        for (_, dep) in &additional_deps {
            self.insert(dep.0, dep.1);

            trace!("{:?} -> {:?}", dep, key);
            self.clone_graph.add_edge(*dep, key, None);
        }
    }

    fn clone_laws(&mut self, ctx: &mut TranslationCtx<'_, 'tcx>, key: (DefId, SubstsRef<'tcx>)) {
        let Some(item) = ctx.tcx.opt_associated_item(key.0) else { return };

        if let Some(self_trait) = ctx.tcx.opt_associated_item(self.self_id) {
            if self_trait.container.id() == item.container.id() {
                return;
            }
        }

        if util::is_trusted(ctx.tcx, self.self_id) || !util::has_body(ctx, self.self_id) {
            return;
        }

        if !self.use_full_clones {
            return;
        }

        let laws = ctx.item(item.container.id()).and_then(|i| i.laws()).unwrap_or(&[]);

        for law in laws {
            trace!("adding law {:?} in {:?}", *law, self.self_id);

            // No way the substitution is correct...
            let law = self.insert(*law, key.1);
            law.public = false;
        }
    }

    pub fn to_clones(&mut self, ctx: &mut ctx::TranslationCtx<'_, 'tcx>) -> Vec<Decl> {
        let mut decls = Vec::new();

        use petgraph::visit::{Topo, Walker};
        let empty = CloneSummary::new();

        // Update the clone graph with any new entries.
        self.update_graph(ctx);

        self.last_cloned = self.names.len();

        debug!(
            "dep_graph nodes={} edges={}",
            self.clone_graph.node_count(),
            self.clone_graph.edge_count()
        );

        // Traverse the dependency graph in topological order to create the minimal amount of
        // clones that are needed. This allows us to share all the nodes that are higher up in
        // the dependency graph.
        // TODO: Ensure that if there is a cycle we emit a nice error.

        let mut topo = Topo::new(&self.clone_graph);
        while let Some(node @ (def_id, subst)) = topo.walk_next(&self.clone_graph) {
            debug!("processing node={:?}", node);

            // Though we pass in a &mut ref, it shouldn't actually be possible to add any new entries..
            let mut clone_subst = base_subst(ctx, self, def_id, subst);

            if self.names.get(&node).unwrap_or_else(|| panic!("{:?}", node)).cloned {
                continue;
            }
            self.names[&node].cloned = true;

            if self.names[&node].kind == Kind::Hidden {
                continue;
            }

            let node_clones = ctx.dependencies(def_id).unwrap_or(&empty);
            for (dep, t, &orig_subst) in self.clone_graph.edges_directed(node, Incoming) {
                trace!("s={:?} t={:?} e={:?}", dep, t, orig_subst);

                let recv_info = match orig_subst {
                    Some(recv_id) => &node_clones[&recv_id],
                    None => continue,
                };

                // Grab the symbols from all dependencies
                let caller_info = &self.names[&dep];
                for sym in refinable_symbols(ctx.tcx, orig_subst.unwrap_or(dep).0) {
                    let elem = sym.to_subst(recv_info, caller_info);
                    // If we are in an interface, then we should not attempt to share
                    // dependencies at all.
                    clone_subst.push(elem);
                }
            }

            // Add any 'additional dependencies'
            for (sym, dep) in &self.names[&node].additional_deps {
                let mut syms = refinable_symbols(ctx.tcx, def_id).filter(|sk| sk.sym() == *sym);
                let sym = syms.next().unwrap();
                assert!(syms.next().is_none());

                let caller_info = &self.names[dep];
                let src = CloneInfo::hidden();
                clone_subst.push(sym.to_subst(&src, caller_info));
            }

            if ctx.item(def_id).map(|i| i.has_axioms()).unwrap_or(false) {
                clone_subst.push(CloneSubst::Axiom(None))
            }

            decls.push(Decl::Clone(DeclClone {
                name: cloneable_name(ctx.tcx, def_id, !self.use_full_clones),
                subst: clone_subst,
                kind: self.names[&node].kind.clone().into(),
            }));
        }

        self.prelude
            .iter_mut()
            .filter(|(_, v)| !(**v))
            .map(|(p, v)| {
                *v = true;
                p
            })
            .map(|q| Decl::UseDecl(Use { name: q.clone() }))
            .chain(decls.into_iter())
            .collect()
    }
}

// Create the substitution used to clone `def_id` with the rustc substitution `subst`.
pub fn base_subst<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Vec<CloneSubst> {
    use heck::SnakeCase;
    use rustc_middle::ty::GenericParamDefKind;

    let trait_params = ctx.tcx.generics_of(def_id);
    let mut clone_subst = Vec::new();

    if subst.is_empty() {
        return Vec::new();
    }

    for ix in 0..trait_params.count() {
        let p = trait_params.param_at(ix, ctx.tcx);
        let ty = subst[ix];
        if let GenericParamDefKind::Type { .. } = p.kind {
            let ty = super::ty::translate_ty(ctx, names, rustc_span::DUMMY_SP, ty.expect_ty());
            clone_subst.push(CloneSubst::Type(p.name.to_string().to_snake_case().into(), ty));
        }
    }

    clone_subst
}

fn cloneable_name(tcx: TyCtxt, def_id: DefId, interface: bool) -> QName {
    use util::ItemType::*;

    // TODO: Refactor.
    match util::item_type(tcx, def_id) {
        Logic | Predicate | Impl => {
            if interface {
                // TODO: this should directly be a function...
                QName { module: Vec::new(), name: interface::interface_name(tcx, def_id) }
            } else {
                module_name(tcx, def_id).into()
            }
        }
        Interface | Program => {
            QName { module: Vec::new(), name: interface::interface_name(tcx, def_id) }
        }
        Trait | Type | AssocTy => module_name(tcx, def_id).into(),
    }
}

enum SymbolKind {
    Val(Symbol),
    Type(Symbol),
    Function(Symbol),
    Predicate(Symbol),
}

impl SymbolKind {
    fn sym(&self) -> Symbol {
        match self {
            SymbolKind::Val(i) => *i,
            SymbolKind::Type(i) => *i,
            SymbolKind::Function(i) => *i,
            SymbolKind::Predicate(i) => *i,
        }
    }

    fn ident(&self) -> Ident {
        match self {
            SymbolKind::Type(_) => ident_of_ty(self.sym()),
            _ => ident_of(self.sym()),
        }
    }

    fn to_subst(self, src: &CloneInfo, tgt: &CloneInfo) -> CloneSubst {
        let id = self.ident();
        match self {
            SymbolKind::Val(_) => CloneSubst::Val(src.qname_raw(id.clone()), tgt.qname_raw(id)),
            SymbolKind::Type(_) => CloneSubst::Type(
                src.qname_raw(id.clone()),
                why3::mlcfg::Type::TConstructor(tgt.qname_raw(id)),
            ),
            SymbolKind::Function(_) => {
                CloneSubst::Function(src.qname_raw(id.clone()), tgt.qname_raw(id))
            }
            SymbolKind::Predicate(_) => {
                CloneSubst::Predicate(src.qname_raw(id.clone()), tgt.qname_raw(id))
            }
        }
    }
}

// Gather the list of symbols that are exported from a DefId in the eyes of Creusot.
// In short:
// - All kinds of functions: function name
// - Traits & Impls: All functions in the trait/impl + all associated types
fn refinable_symbols(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Box<dyn Iterator<Item = SymbolKind> + 'tcx> {
    use std::iter::{self, *};
    use util::ItemType::*;
    match util::item_type(tcx, def_id) {
        Logic => Box::new(iter::once(SymbolKind::Function(tcx.item_name(def_id)))),
        Predicate => Box::new(iter::once(SymbolKind::Predicate(tcx.item_name(def_id)))),
        Interface | Program => Box::new(iter::once(SymbolKind::Val(tcx.item_name(def_id)))),
        AssocTy => match tcx.associated_item(def_id).container {
            ty::TraitContainer(_) => box once(SymbolKind::Type(tcx.item_name(def_id))),
            ty::ImplContainer(_) => box empty(),
        },
        Trait | Impl => unreachable!(),
        Type => unreachable!(),
    }
}

// A basic visitor which can be used to gether ProjectionTys containd in
// a foldable struct
struct ProjectionTyVisitor<'a, 'tcx> {
    f: Box<dyn FnMut(ProjectionTy<'tcx>) + 'a>,
}

impl TypeVisitor<'tcx> for ProjectionTyVisitor<'a, 'tcx> {
    fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
        None
    }

    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        if let TyKind::Projection(t) = t.kind() {
            (*self.f)(*t)
        }
        ControlFlow::CONTINUE
    }
}
