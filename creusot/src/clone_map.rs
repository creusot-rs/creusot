use std::ops::ControlFlow;

use indexmap::IndexMap;

use petgraph::graphmap::DiGraphMap;
use petgraph::EdgeDirection::Incoming;
use why3::declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use};
use why3::{Ident, QName};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    self,
    fold::{TypeFoldable, TypeVisitor},
    subst::{InternalSubsts, Subst, SubstsRef},
    AssocKind, ProjectionTy, Ty, TyCtxt, TyKind,
};
use rustc_span::Symbol;

use heck::CamelCase;

use crate::ctx::{self, *};
use crate::translation::ty::translate_ty;
use crate::translation::{interface, traits};
use crate::util::{self, method_name};

// Prelude modules
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PreludeModule {
    Int,
    Int32,
    Int64,
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
            PreludeModule::Int32 => QName::from_string("mach.int.Int32").unwrap(),
            PreludeModule::Int64 => QName::from_string("mach.int.Int64").unwrap(),
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
    projections: Vec<(DefId, Ty<'tcx>)>,
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
        CloneInfo { kind: Kind::Named(name), projections: Vec::new(), cloned: false, public }
    }

    fn hidden() -> Self {
        CloneInfo { kind: Kind::Hidden, projections: Vec::new(), cloned: false, public: false }
    }

    pub fn mk_export(&mut self) {
        self.kind = Kind::Export;
    }

    pub fn add_projection(&mut self, proj: (DefId, Ty<'tcx>)) {
        self.projections.push(proj);
    }

    // TODO: When traits stop holding all functions we can remove the last two arguments
    pub fn qname(&self, tcx: TyCtxt, def_id: DefId) -> QName {
        self.qname_raw(method_name(tcx, def_id))
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
    pub fn new(tcx: TyCtxt<'tcx>, use_full_clones: bool) -> Self {
        let names = IndexMap::new();
        CloneMap {
            tcx,
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

    pub fn insert(&mut self, mut def_id: DefId, subst: SubstsRef<'tcx>) -> &mut CloneInfo<'tcx> {
        if let Some(it) = self.tcx.opt_associated_item(def_id) {
            def_id = match it.container {
                ty::TraitContainer(id) => id,
                ty::ImplContainer(id) => {
                    if self.tcx.trait_id_of_impl(id).is_some() {
                        id
                    } else {
                        def_id
                    }
                }
            };
        };

        self.insert_raw(def_id, subst)
    }

    // Bad.
    pub(crate) fn insert_raw(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
    ) -> &mut CloneInfo<'tcx> {
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

    pub fn clone_self(&mut self, mut self_id: DefId) {
        let subst = InternalSubsts::identity_for_item(self.tcx, self_id);
        let subst = self.tcx.erase_regions(subst);

        debug!("cloning self: {:?}", (self_id, subst));

        if let Some(it) = self.tcx.opt_associated_item(self_id) {
            self_id = self_id

            // match it.container {
            //     ty::TraitContainer(id) => id,
            //     _ => self_id,
            //     // ty::ImplContainer(id) => {
                //     if self.tcx.trait_id_of_impl(id).is_some() {
                //         id
                //     } else {
                //         self_id
                //     }
                // }
            // };
        };
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
        let empty = CloneSummary::new();

        while i < self.names.len() {
            let (&key, clone_info) = self.names.get_index(i).unwrap();
            i += 1;
            trace!("{:?} is public={:?}", key, clone_info.public);

            if clone_info.kind == Kind::Hidden {
                continue;
            }

            self.clone_graph.add_node(key);
            {
                // Gather all the associated types used in a substitution so we can force an edge
                let mut visitor = ProjectionTyVisitor {
                    f: Box::new(|pty: ProjectionTy<'tcx>| {
                        let trait_id = pty.trait_def_id(self.tcx);
                        trace!("adding projection edge=({:?}, {:?})", trait_id, pty.substs);
                        self.clone_graph.add_edge((trait_id, pty.substs), key, None);
                    }),
                };
                key.1.visit_with(&mut visitor);

                // If we have an additional projections, check if their type contains a further associated type.
                for (_, t) in &clone_info.projections {
                    t.visit_with(&mut visitor);
                }
            }
            debug!(
                "{:?} has {:?} dependencies",
                key,
                ctx.dependencies(key.0).map(|d| d.len()).unwrap_or(5)
            );
            for (dep, info) in ctx.dependencies(key.0).unwrap_or(&empty) {
                if !self.use_full_clones && !info.public {
                    continue;
                }
                trace!("adding dependency {:?}", dep);

                let orig = dep;
                let dep = (dep.0, dep.1.subst(self.tcx, key.1));
                trace!("substituted: {:?}", dep);
                let dep = match traits::resolve_opt(ctx.tcx, ctx.tcx.param_env(key.0), dep.0, dep.1)
                {
                    Some(dep) => (dep),
                    None => (dep),
                };

                // Inherit the visibility of the parent, becoming public if at least one
                // dependency is public.
                let dep_info = self.insert(dep.0, dep.1);
                dep_info.public |= info.public;

                // Skip reflexive edges
                if dep == key {
                    continue;
                }

                trace!("edge {:?} -> {:?}", dep, key);
                self.clone_graph.add_edge(dep, key, Some(*orig));
            }
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
            ctx.translate(def_id);

            // Though we pass in a &mut ref, it shouldn't actually be possible to add any new entries..
            let mut clone_subst = base_subst(ctx, self, def_id, subst);

            if self.names[&node].cloned {
                continue;
            }
            self.names[&node].cloned = true;

            if self.names[&node].kind == Kind::Hidden {
                continue;
            }

            // Add all associated type projections to the substitution.
            // We must be ordered topologically *after* whatever occurs on the RHS of the projection
            for proj in &std::mem::take(&mut self.names[&node].projections) {
                let ty = translate_ty(ctx, self, rustc_span::DUMMY_SP, proj.1);
                clone_subst.push(CloneSubst::Type(
                    crate::translation::ty::ty_name(ctx.tcx, proj.0).into(),
                    ty,
                ));
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
                    let elem = match sym {
                        SymbolKind::Val(n) => CloneSubst::Val(
                            recv_info.qname_raw(n.clone()),
                            caller_info.qname_raw(n),
                        ),
                        SymbolKind::Type(t) => CloneSubst::Type(
                            recv_info.qname_raw(t.clone()),
                            why3::mlcfg::Type::TConstructor(caller_info.qname_raw(t)),
                        ),
                        SymbolKind::Function(f) => CloneSubst::Function(
                            recv_info.qname_raw(f.clone()),
                            caller_info.qname_raw(f),
                        ),
                        SymbolKind::Predicate(p) => CloneSubst::Predicate(
                            recv_info.qname_raw(p.clone()),
                            caller_info.qname_raw(p),
                        ),
                    };
                    // If we are in an interface, then we should not attempt to share
                    // dependencies at all.
                    clone_subst.push(elem);
                }
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
    let qname = translate_value_id(tcx, def_id);
    use util::ItemType::*;

    // TODO: Refactor.
    match util::item_type(tcx, def_id) {
        Logic | Predicate | Pure | Impl => {
            if interface {
                // TODO: this should directly be a function...
                QName { module: Vec::new(), name: interface::interface_name(tcx, def_id) }
            } else {
                qname.module_ident().unwrap_or(&qname.name()).clone().into()
            }
        }
        Interface | Program => {
            QName { module: Vec::new(), name: interface::interface_name(tcx, def_id) }
        }
        Trait => qname,
        Type => unreachable!(),
    }
}

enum SymbolKind {
    Val(Ident),
    Type(Ident),
    Function(Ident),
    Predicate(Ident),
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
        Logic => Box::new(iter::once(SymbolKind::Function(method_name(tcx, def_id)))),
        Predicate => Box::new(iter::once(SymbolKind::Predicate(method_name(tcx, def_id)))),
        Interface | Program => Box::new(iter::once(SymbolKind::Val(method_name(tcx, def_id)))),
        Pure => Box::new(
            iter::once(SymbolKind::Function(method_name(tcx, def_id))), // .chain(iter::once(SymbolKind::Val(method_name(tcx, def_id)))),
        ),
        Trait => {
            Box::new(traits::associated_items(tcx, def_id).flat_map(move |a| {
                let it: Box<dyn Iterator<Item = _> + 'tcx> = match a.kind {
                    AssocKind::Fn => match util::item_type(tcx, a.def_id) {
                        Logic => box once(SymbolKind::Function(method_name(tcx, a.def_id))),
                        Predicate => box once(SymbolKind::Predicate(method_name(tcx, a.def_id))),
                        Program => box once(SymbolKind::Val(method_name(tcx, a.def_id))),
                        Pure => box [
                            SymbolKind::Function(method_name(tcx, a.def_id)),
                            SymbolKind::Val(method_name(tcx, a.def_id)),
                        ]
                        .into_iter(), // wrong,
                        _ => unreachable!(),
                    },
                    AssocKind::Type => box once(SymbolKind::Type(
                        crate::translation::ty::ty_name(tcx, a.def_id).into(),
                    )),
                    AssocKind::Const => unimplemented!("Tried to clone associated constant"),
                };
                it
            }))
        }
        Impl => Box::new(tcx.associated_items(def_id).in_definition_order().filter_map(move |a| {
            match a.kind {
                AssocKind::Fn => match util::item_type(tcx, a.def_id) {
                    Logic => Some(SymbolKind::Function(method_name(tcx, a.def_id))),
                    Predicate => Some(SymbolKind::Predicate(method_name(tcx, a.def_id))),
                    Program => Some(SymbolKind::Val(method_name(tcx, a.def_id))),
                    _ => unreachable!(),
                },
                AssocKind::Type => None,
                AssocKind::Const => None,
            }
        })),
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
