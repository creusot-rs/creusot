use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{
        self,
        subst::{InternalSubsts, Subst, SubstsRef},
        DefIdTree, EarlyBinder, ProjectionTy, Ty, TyCtxt, TyKind, TypeFoldable, TypeSuperFoldable,
        TypeVisitor,
    },
    span::{Symbol, DUMMY_SP},
};
use heck::CamelCase;
use indexmap::{IndexMap, IndexSet};
use petgraph::{graphmap::DiGraphMap, visit::DfsPostOrder, EdgeDirection::Outgoing};
use why3::{
    declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use},
    Ident, QName,
};

use crate::{
    ctx::{self, *},
    translation::{interface, traits},
    util::{self, ident_of, ident_of_ty, item_name},
};

// Prelude modules
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PreludeModule {
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
    Single,
    Double,
    Prelude,
    Ref,
    Seq,
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
            PreludeModule::Int128 => QName::from_string("prelude.Int128").unwrap(),
            PreludeModule::UInt8 => QName::from_string("prelude.UInt8").unwrap(),
            PreludeModule::UInt16 => QName::from_string("prelude.UInt16").unwrap(),
            PreludeModule::UInt32 => QName::from_string("mach.int.UInt32").unwrap(),
            PreludeModule::UInt64 => QName::from_string("mach.int.UInt64").unwrap(),
            PreludeModule::UInt128 => QName::from_string("prelude.UInt128").unwrap(),
            PreludeModule::Char => QName::from_string("string.Char").unwrap(),
            PreludeModule::Single => QName::from_string("floating_point.Single").unwrap(),
            PreludeModule::Double => QName::from_string("floating_point.Double").unwrap(),
            PreludeModule::Prelude => QName::from_string("prelude.Prelude").unwrap(),
            PreludeModule::Ref => QName::from_string("Ref").unwrap(),
            PreludeModule::Seq => QName::from_string("seq.Seq").unwrap(),
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
    // TODO: Push the graph into an opaque type with tight api boundary
    // Graph which is used to calculate the full clone set
    clone_graph: DiGraphMap<DepNode<'tcx>, IndexSet<(Kind, SymbolKind)>>,
    // Index of the last cloned entry
    last_cloned: usize,

    // Internal state to determine whether clones should be public or not
    public: bool,
}

impl<'tcx> Drop for CloneMap<'tcx> {
    fn drop(&mut self) {
        if self.last_cloned != self.names.len() {
            debug!(
                "Dropping clone map with un-emitted clones. {:?} clones emitted of {:?} total {:?}",
                self.last_cloned,
                self.names.len(),
                self.self_id,
            );

            debug_assert!(false);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum DepNode<'tcx> {
    Type(Ty<'tcx>),
    Dep(CloneNode<'tcx>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable, Hash)]
enum Kind {
    Named(Symbol),
    Hidden,
    Export,
    // Use,
}

impl Kind {
    pub fn qname_ident(&self, method: Ident) -> QName {
        let module = match &self {
            Kind::Named(name) => vec![name.to_string().into()],
            _ => Vec::new(),
        };
        QName { module, name: method }
    }
}

use creusot_rustc::macros::{TyDecodable, TyEncodable};

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
enum CloneOpacity {
    Transparent,
    Opaque,
    Default,
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct CloneInfo<'tcx> {
    kind: Kind,
    additional_deps: Vec<(Symbol, (DefId, SubstsRef<'tcx>))>,
    cloned: bool,
    public: bool,
    opaque: CloneOpacity,
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

impl<'tcx> CloneInfo<'tcx> {
    fn from_name(name: Symbol, public: bool) -> Self {
        CloneInfo {
            kind: Kind::Named(name),
            additional_deps: Vec::new(),
            cloned: false,
            public,
            opaque: CloneOpacity::Default,
        }
    }

    fn hidden() -> Self {
        CloneInfo {
            kind: Kind::Hidden,
            additional_deps: Vec::new(),
            cloned: false,
            public: false,
            opaque: CloneOpacity::Default,
        }
    }

    pub fn mk_export(&mut self) {
        self.kind = Kind::Export;
    }

    pub fn add_dep(&mut self, tcx: TyCtxt<'tcx>, name: Symbol, mut dep: (DefId, SubstsRef<'tcx>)) {
        dep.1 = tcx.erase_regions(dep.1);
        self.additional_deps.push((name, dep));
    }

    pub fn opaque(&mut self) {
        self.opaque = CloneOpacity::Opaque;
    }

    pub fn transparent(&mut self) {
        self.opaque = CloneOpacity::Transparent;
    }

    // TODO: When traits stop holding all functions we can remove the last two arguments
    pub fn qname(&self, tcx: TyCtxt, def_id: DefId) -> QName {
        self.qname_ident(match tcx.def_kind(def_id) {
            // DefKind::Closure => Ident::build("closure"),
            _ => item_name(tcx, def_id),
        })
    }

    pub fn qname_sym(&self, sym: creusot_rustc::span::symbol::Symbol) -> QName {
        self.qname_ident(sym.to_string().into())
    }

    pub fn qname_ident(&self, method: Ident) -> QName {
        self.kind.qname_ident(method)
    }
}

impl<'tcx> CloneMap<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, self_id: DefId, use_full_clones: bool) -> Self {
        let names = IndexMap::new();
        let mut c = CloneMap {
            tcx,
            self_id,
            names,
            name_counts: Default::default(),
            prelude: IndexMap::new(),
            use_full_clones,
            clone_graph: DiGraphMap::new(),
            last_cloned: 0,
            public: false,
        };
        c.names.insert(c.self_key(), CloneInfo::hidden());
        c
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

    pub fn with_public_clones<F, A>(&mut self, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        let public = std::mem::replace(&mut self.public, true);
        let ret = f(self);
        self.public = public;
        ret
    }

    pub fn insert(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> &mut CloneInfo<'tcx> {
        let subst = self.tcx.erase_regions(subst);

        let (def_id, subst) = self.closure_hack(def_id, subst);

        self.names.entry((def_id, subst)).or_insert_with(|| {
            let base_sym = match util::item_type(self.tcx, def_id) {
                ItemType::Impl => self.tcx.item_name(self.tcx.trait_id_of_impl(def_id).unwrap()),
                ItemType::Closure => Symbol::intern(&format!(
                    "closure{}",
                    self.tcx.def_path(def_id).data.last().unwrap().disambiguator
                )),
                _ => self.tcx.item_name(def_id),
            };

            let base = Symbol::intern(&base_sym.as_str().to_camel_case());
            let count: usize = *self.name_counts.entry(base).and_modify(|c| *c += 1).or_insert(0);
            debug!("inserting {:?} {:?} as {}{}", def_id, subst, base, count);

            let info =
                CloneInfo::from_name(Symbol::intern(&format!("{}{}", base, count)), self.public);
            info
        })
    }

    fn self_key(&self) -> (DefId, SubstsRef<'tcx>) {
        use creusot_rustc::hir::def::DefKind;
        let subst = match self.tcx.def_kind(self.self_id) {
            DefKind::Closure => match self.tcx.type_of(self.self_id).kind() {
                TyKind::Closure(_, subst) => subst,
                _ => unreachable!(),
            },
            _ => InternalSubsts::identity_for_item(self.tcx, self.self_id),
        };

        let subst = self.tcx.erase_regions(subst);
        (self.self_id, subst)
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

    fn closure_hack(&self, def_id: DefId, subst: SubstsRef<'tcx>) -> (DefId, SubstsRef<'tcx>) {
        if self.tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id)
        {
            debug!("closure_hack: {:?} {:?}", self.self_id, def_id);
            let self_ty = subst.types().nth(1).unwrap();
            if let TyKind::Closure(id, csubst) = self_ty.kind() {
                return (*id, csubst);
            }
        };

        if self.tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
        {
            let self_ty = subst.types().nth(0).unwrap();
            if let TyKind::Closure(id, csubst) = self_ty.kind() {
                return (*id, csubst);
            }
        }

        (def_id, subst)
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

            if key != self.self_key() {
                self.add_graph_edge(DepNode::Dep(self.self_key()), DepNode::Dep(key));
            }

            if self.names[&key].kind == Kind::Hidden {
                continue;
            }

            ctx.translate(key.0);

            debug!(
                "{:?} {:?} has {:?} dependencies",
                self.names[&key].kind,
                key,
                ctx.dependencies(key.0).map(|d| d.len())
            );
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
        // Check the substitution for dependencies on closures
        for ty in key.1.types() {
            if let TyKind::Closure(id, subst) = ty.kind() {
                self.insert(*id, subst);
                // Sketchy... shouldn't we need to do something to subst?
                self.add_graph_edge(DepNode::Dep(key), DepNode::Dep((*id, subst)));
            }
        }

        walk_projections(key.1, |pty: &ProjectionTy<'tcx>| {
            let dep = self.resolve_dep(ctx, (pty.item_def_id, pty.substs));

            if let DepNode::Dep((defid, subst)) = dep {
                trace!("inserting projection dependency {:?}", dep);
                self.insert(defid, subst);
            }

            self.add_graph_edge(DepNode::Dep(key), dep);
        });

        let key_public = self.names[&key].public;
        // Whether we are treating this clone as an opaque symbol
        let opaque_clone = !self.use_full_clones || self.names[&key].opaque == CloneOpacity::Opaque;
        for (dep, info) in ctx.dependencies(key.0).iter().flat_map(|i| i.iter()) {
            if opaque_clone && !info.public {
                continue;
            }
            trace!("adding dependency {:?} {:?}", dep, info.public);

            let orig = dep;

            let dep = self.resolve_dep(ctx, (dep.0, EarlyBinder(dep.1).subst(self.tcx, key.1)));

            if let DepNode::Dep((defid, subst)) = dep {
                trace!("inserting dependency {:?}", dep);
                self.insert(defid, subst).public |= key_public && info.public;
            }

            // Skip reflexive edges
            if dep == DepNode::Dep(key) {
                continue;
            }

            let edge_set = self.add_graph_edge(DepNode::Dep(key), dep);
            if let Some(sym) = refineable_symbol(ctx.tcx, orig.0) {
                edge_set.insert((info.kind, sym));
            }
        }
    }

    // Adds a dependency from `user` on `prov` for the symbol `sym`.
    fn add_graph_edge(
        &mut self,
        user: DepNode<'tcx>,
        prov: DepNode<'tcx>,
    ) -> &mut IndexSet<(Kind, SymbolKind)> {
        let k1 = if let DepNode::Dep(d1) = user { Some(&self.names[&d1].kind) } else { None };
        let k2 = if let DepNode::Dep(d2) = prov { Some(&self.names[&d2].kind) } else { None };
        debug!("{k1:?} = {:?} --> {k2:?} = {:?}", user, prov);

        if let None = self.clone_graph.edge_weight_mut(user, prov) {
            self.clone_graph.add_edge(user, prov, IndexSet::new());
        };

        self.clone_graph.edge_weight_mut(user, prov).unwrap()
    }

    // Given an initial substitution, find out the substituted and resolved version of the dependency `dep`.
    // This will attempt to normalize traits and associated types if the substitution provides enough
    // information.
    fn resolve_dep(
        &self,
        ctx: &TranslationCtx<'_, 'tcx>,
        dep: (DefId, SubstsRef<'tcx>),
    ) -> DepNode<'tcx> {
        let param_env = ctx.param_env(self.self_id);
        let dep = self.tcx.try_normalize_erasing_regions(param_env, dep).unwrap_or(dep);

        let resolved = traits::resolve_opt(ctx.tcx, param_env, dep.0, dep.1).unwrap_or(dep);
        let resolved = self.closure_hack(resolved.0, resolved.1);

        if util::item_type(self.tcx, resolved.0) == ItemType::AssocTy
            && self.tcx.trait_of_item(resolved.0).is_some()
        {
            let proj_ty = ProjectionTy { item_def_id: dep.0, substs: dep.1 };
            let ty = self.tcx.mk_ty(TyKind::Projection(proj_ty));

            let normed = self.tcx.try_normalize_erasing_regions(param_env, ty);
            trace!("normed {ty:?} into {normed:?}");
            if let Ok(normed) = normed && ty != normed {
                match normed.kind() {
                    TyKind::Projection(pty) => return DepNode::Dep((pty.item_def_id, pty.substs)),
                    _ => return DepNode::Type(normed),
                }
            }
        };

        return DepNode::Dep(resolved);
    }

    fn clone_additional_deps(&mut self, key: (DefId, SubstsRef<'tcx>)) {
        let additional_deps = self.names[&key].additional_deps.clone();
        for (sym, dep) in &additional_deps {
            self.insert(dep.0, dep.1);
            let sym = refineable_symbol(self.tcx, key.0).filter(|sk| sk.sym() == *sym).unwrap();

            self.add_graph_edge(DepNode::Dep(key), DepNode::Dep(*dep)).insert((Kind::Hidden, sym));
        }
    }

    fn clone_laws(&mut self, ctx: &mut TranslationCtx<'_, 'tcx>, key: (DefId, SubstsRef<'tcx>)) {
        let Some(item) = ctx.tcx.opt_associated_item(key.0) else { return };

        // Dont clone laws into the trait / impl which defines them.
        if let Some(self_trait) = ctx.tcx.opt_associated_item(self.self_id) {
            if self_trait.container.id() == item.container.id() {
                return;
            }
        }

        // If the function we are cloning into is `#[trusted]` there is no need for laws.
        // Similarily, if it has no body, there will be no proofs.
        if util::is_trusted(ctx.tcx, self.self_id) || !util::has_body(ctx, self.self_id) {
            return;
        }

        if !self.use_full_clones {
            return;
        }

        ctx.translate(item.container.id());
        let laws = ctx.item(item.container.id()).and_then(|i| i.laws()).unwrap_or(&[]);

        for law in laws {
            trace!("adding law {:?} in {:?}", *law, self.self_id);

            // No way the substitution is correct...
            let law = self.insert(*law, key.1);
            law.public = false;
        }
    }

    pub fn to_clones(&mut self, ctx: &mut ctx::TranslationCtx<'_, 'tcx>) -> Vec<Decl> {
        debug!("emitting clones for {:?}", self.self_id);
        let mut decls = Vec::new();

        use petgraph::visit::Walker;

        // Update the clone graph with any new entries.
        self.update_graph(ctx);

        debug!(
            "dep_graph processed={} nodes={} edges={}",
            self.last_cloned,
            self.clone_graph.node_count(),
            self.clone_graph.edge_count()
        );

        self.last_cloned = self.names.len();

        // Broken because of closures which share a defid for the type *and* function
        // debug_assert!(!is_cyclic_directed(&self.clone_graph), "clone graph for {:?} is cyclic", self.self_id );

        let mut topo = DfsPostOrder::new(&self.clone_graph, DepNode::Dep(self.self_key()));
        while let Some(node) = topo.walk_next(&self.clone_graph) {
            let DepNode::Dep(node @ (def_id, subst)) = node else { continue };
            debug!("processing node {:?}", self.names[&node].kind);

            // Though we pass in a &mut ref, it shouldn't actually be possible to add any new entries..
            let mut clone_subst = base_subst(ctx, self, def_id, subst);

            if self.names[&node].cloned {
                continue;
            }
            self.names[&node].cloned = true;

            if self.names[&node].kind == Kind::Hidden {
                continue;
            }

            let outbound: Vec<_> =
                self.clone_graph.neighbors_directed(DepNode::Dep(node), Outgoing).collect();

            // Grab definitions from all of our dependencies
            for dep in outbound {
                let syms = &self.clone_graph[(DepNode::Dep(node), dep)];
                trace!("s={:?} t={:?} e={:?}", dep, node, syms);

                match dep {
                    DepNode::Type(ty) => {
                        let (nm, sym) = syms.iter().next().unwrap(); // Type nodes only have have exactly one symbol

                        let ty_name = nm.qname_ident(sym.ident());
                        let ty = super::ty::translate_ty(ctx, self, DUMMY_SP, ty);
                        clone_subst.push(CloneSubst::Type(ty_name, ty))
                    }
                    DepNode::Dep(dep) => {
                        for (nm, sym) in syms {
                            let elem = sym.to_subst(*nm, self.names[&dep].kind);
                            clone_subst.push(elem);
                        }
                    }
                }
            }

            let use_axioms = match self.names[&node].opaque {
                CloneOpacity::Opaque | CloneOpacity::Default => {
                    ctx.item(def_id).map(|i| i.has_axioms()).unwrap_or(false)
                }
                _ => false,
            };
            if use_axioms {
                clone_subst.push(CloneSubst::Axiom(None))
            }

            let interface = match self.names[&node].opaque {
                CloneOpacity::Opaque => true,
                CloneOpacity::Default => !self.use_full_clones,
                CloneOpacity::Transparent => false,
            };

            debug!(
                "emit clone node={node:?} name={:?} as={:?}",
                cloneable_name(ctx.tcx, def_id, interface),
                self.names[&node].kind.clone()
            );

            decls.push(Decl::Clone(DeclClone {
                name: cloneable_name(ctx.tcx, def_id, interface),
                subst: clone_subst,
                kind: self.names[&node].kind.clone().into(),
            }));
        }

        // debug_assert!(topo.finished.len() >= self.names.len(), "missed a clone in {:?}", self.self_id);

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
    mut def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Vec<CloneSubst> {
    use creusot_rustc::middle::ty::GenericParamDefKind;
    use heck::SnakeCase;
    loop {
        if ctx.tcx.is_closure(def_id) {
            def_id = ctx.tcx.parent(def_id);
        } else {
            break;
        }
    }
    let trait_params = ctx.tcx.generics_of(def_id);
    let mut clone_subst = Vec::new();

    if subst.is_empty() {
        return Vec::new();
    }

    for ix in 0..trait_params.count() {
        let p = trait_params.param_at(ix, ctx.tcx);
        let ty = subst[ix];
        if let GenericParamDefKind::Type { .. } = p.kind {
            let ty =
                super::ty::translate_ty(ctx, names, creusot_rustc::span::DUMMY_SP, ty.expect_ty());
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
        Interface | Program | Closure => {
            QName { module: Vec::new(), name: interface::interface_name(tcx, def_id) }
        }
        Constant | Trait | Type | AssocTy => module_name(tcx, def_id).into(),
        Unsupported(_) => unreachable!(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
        }
    }
}

// Identify the name and kind of symbol which can be refined in a given defid
fn refineable_symbol<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<SymbolKind> {
    use util::ItemType::*;
    match util::item_type(tcx, def_id) {
        Logic => Some(SymbolKind::Function(tcx.item_name(def_id))),
        Predicate => Some(SymbolKind::Predicate(tcx.item_name(def_id))),
        Interface | Program => Some(SymbolKind::Val(tcx.item_name(def_id))),
        AssocTy => match tcx.associated_item(def_id).container {
            ty::TraitContainer(_) => Some(SymbolKind::Type(tcx.item_name(def_id))),
            ty::ImplContainer(_) => None,
        },
        Trait | Impl => unreachable!("trait blocks have no refinable symbols"),
        Type => unreachable!("types have no refinable symbols"),
        _ => unreachable!(),
    }
}

// Walk all the projections in a substitution so we can add dependencies on them
fn walk_projections<'tcx, T: TypeFoldable<'tcx>, F: FnMut(&ProjectionTy<'tcx>)>(s: T, f: F) {
    s.visit_with(&mut ProjectionTyVisitor { f, p: std::marker::PhantomData });
}

struct ProjectionTyVisitor<'tcx, F: FnMut(&ProjectionTy<'tcx>)> {
    f: F,
    p: std::marker::PhantomData<&'tcx ()>,
}

impl<'tcx, F: FnMut(&ProjectionTy<'tcx>)> TypeVisitor<'tcx> for ProjectionTyVisitor<'tcx, F> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        match t.kind() {
            TyKind::Projection(pty) => {
                (self.f)(pty);
                t.super_visit_with(self)
            }
            _ => t.super_visit_with(self),
        }
    }
}
