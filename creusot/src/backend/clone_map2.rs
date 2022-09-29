use std::collections::HashSet;

use creusot_rustc::{
    hir::def_id::DefId,
    macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable},
    middle::ty::{
        subst::{Subst, SubstsRef},
        EarlyBinder, TypeVisitable,
    },
    resolve::Namespace,
    span::{Symbol, DUMMY_SP},
};
use heck::CamelCase;
use indexmap::IndexMap;
use petgraph::{
    graphmap::DiGraphMap,
    visit::{DfsPostOrder, Walker},
    EdgeDirection::Outgoing,
};
use rustc_middle::{
    middle::dependency_format::Dependencies,
    ty::{
        subst::{GenericArgKind, InternalSubsts},
        DefIdTree, Ty, TyCtxt, TyKind, TypeVisitor,
    },
};
use util::ItemType;
use why3::{
    declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use},
    QName,
};

use crate::{
    ctx::TranslationCtx,
    specification::typing::super_visit_term,
    translation::{
        interface,
        specification::typing::{Term, TermKind, TermVisitor},
        traits::resolve_opt,
    },
    util::{self, item_name, item_qname, item_type, module_name, pre_sig_of},
};

// The clone wars are over
// Implements a simpler version of CloneMap, split as two operations: gathering all the 'monomorphic' instances of functions / types used
// and a second why3 specific pass turning that into clones (and later not into clones!)

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug, PartialOrd, Ord, TypeFoldable, TypeVisitable)]
pub enum Dependency<'tcx> {
    // A normal, good Rust function or type
    Item(DefId, SubstsRef<'tcx>),
    // Cannot be a tuple, adt or other composite type.
    // Can be, &mut, &, *mut, [T], [T; N], u32, i32, bool, etc..
    BaseTy(Ty<'tcx>),
}

// Depending on where we are cloning from we will only want to keep
// all or some of our dependencies
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug, PartialOrd, Ord, TypeFoldable, TypeVisitable)]
pub enum DepLevel {
    Body,
    Signature,
}

// Temporary to start testing
// Eventually dependency tracking should probably move into main part of crate?
fn get_immediate_deps<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    match item_type(ctx.tcx, def_id) {
        ItemType::Type => {
            let substs = InternalSubsts::identity_for_item(ctx.tcx, def_id);
            let tys = ctx
                .adt_def(def_id)
                .all_fields()
                .map(|f| f.ty(ctx.tcx, substs))
                .flat_map(|fld| fld.walk());

            let mut v = Vec::new();

            for arg in tys {
                match arg.unpack() {
                    GenericArgKind::Type(ty) => match ty.kind() {
                        TyKind::Adt(def, sub) => {
                            v.push((DepLevel::Body, Dependency::Item(def.did(), *sub)))
                        }
                        _ => {}
                    },
                    GenericArgKind::Lifetime(_) => {}
                    a => panic!("{a:?}"),
                }
            }
            v
        }
        ItemType::Logic | ItemType::Predicate
            if def_id.is_local()
                && !util::is_trusted(ctx.tcx, def_id)
                && util::has_body(ctx, def_id) =>
        {
            term_dependencies(ctx, def_id)
        }
        _ => ctx
            .dependencies(def_id)
            // Wrong.
            .map(|i| {
                i.keys()
                    .cloned()
                    .map(|i| (DepLevel::Signature, Dependency::Item(i.0, i.1)))
                    .collect()
            })
            .unwrap_or_default(),
    }
}

fn term_dependencies<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    struct Dependencies<'tcx> {
        deps: Vec<(DepLevel, Dependency<'tcx>)>,
        level: DepLevel,
    }

    impl<'tcx> TermVisitor<'tcx> for Dependencies<'tcx> {
        fn visit_term(&mut self, term: &Term<'tcx>) {
            match &term.kind {
                TermKind::Item(id, subst) => {
                    self.deps.push((self.level, Dependency::Item(*id, subst)))
                }
                TermKind::Call { id, subst, fun: _, args: _ } => {
                    self.deps.push((self.level, Dependency::Item(*id, subst)))
                }
                TermKind::Constructor { adt: _, variant: _, fields: _ } => {
                    if let TyKind::Adt(def, subst) = term.ty.kind() {
                        self.deps.push((self.level, Dependency::Item(def.did(), subst)))
                    } else {
                        unreachable!()
                    }
                }
                _ => {}
            };
            super_visit_term(term, self)
        }
    }

    impl<'tcx> TypeVisitor<'tcx> for Dependencies<'tcx> {
        fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
            match t.kind() {
                TyKind::Adt(def, sub) => {
                    self.deps.push((self.level, Dependency::Item(def.did(), *sub)))
                }
                TyKind::Projection(pty) => {
                    self.deps.push((self.level, Dependency::Item(pty.item_def_id, pty.substs)))
                }
                _ => {}
            };
            std::ops::ControlFlow::Continue(())
        }
    }

    let mut deps = Dependencies { deps: Vec::new(), level: DepLevel::Signature };

    let sig = pre_sig_of(ctx, def_id);
    sig.contract.terms().for_each(|t| {
        deps.visit_term(t);
    });
    sig.visit_with(&mut deps);

    deps.level = DepLevel::Body;

    if let Some(term) = ctx.term(def_id) {
        deps.visit_term(term);
    }
    deps.deps
}

#[derive(Default)]
pub struct MonoGraph<'tcx> {
    graph: DiGraphMap<Dependency<'tcx>, (DepLevel, Option<(DefId, SubstsRef<'tcx>)>)>,
    level: IndexMap<Dependency<'tcx>, DepLevel>,
    // roots?
}

impl<'tcx> MonoGraph<'tcx> {}

// TODO: should take graph by `&mut` and not take the root def_id directly? (stored in graph?) should instead take a type
// which can have dependencies or a list of dependencies to traverse
pub fn collect<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> MonoGraph<'tcx> {
    let root = Dependency::Item(def_id, InternalSubsts::identity_for_item(ctx.tcx, def_id));
    let mut to_visit = vec![root];
    let mut finished = HashSet::new();
    let param_env = ctx.param_env(def_id);

    let mut graph = DiGraphMap::default();
    while let Some(next) = to_visit.pop() {
        if !finished.insert(next) {
            // Already visited
            continue;
        }
        graph.add_node(next);
        let Dependency::Item(id, subst) = next else { continue };
        ctx.translate(id);

        let to_add = EarlyBinder(get_immediate_deps(ctx, id)).subst(ctx.tcx, subst);

        for (lvl, dep) in to_add {
            let Dependency::Item(id, subst) = dep else {
                graph.add_edge(next, dep, (lvl, None));
                continue
            };

            let tgt = if let Some(tgt) = closure_hack(ctx.tcx, def_id, subst) {
                tgt
            } else if can_resolve(ctx, (id, subst)) {
                resolve_opt(ctx.tcx, param_env, id, subst).unwrap()
            } else {
                ctx.normalize_erasing_regions(param_env, (id, subst))
            };

            graph.add_edge(next, Dependency::Item(tgt.0, tgt.1), (lvl, Some((id, subst))));

            to_visit.push(Dependency::Item(tgt.0, tgt.1));
        }
    }

    // Color the nodes
    let mut level: IndexMap<_, DepLevel> = IndexMap::default();
    for (_, tgt, (lvl, _)) in graph.all_edges() {
        eprintln!("{tgt:?} to {lvl:?}");
        level.entry(tgt).and_modify(|a| *a = (*a).max(*lvl)).or_insert(*lvl);
    }

    MonoGraph { graph, level }
}

fn closure_hack<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id)
    {
        debug!("closure_hack: {:?}", def_id);
        let self_ty = subst.types().nth(1).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return Some((*id, csubst));
        }
    };

    if tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
    {
        let self_ty = subst.types().nth(0).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return Some((*id, csubst));
        }
    }

    None
}

fn can_resolve<'tcx>(ctx: &mut TranslationCtx<'tcx>, dep: (DefId, SubstsRef<'tcx>)) -> bool {
    ctx.trait_of_item(dep.0).is_some()
}

#[derive(Debug)]
pub struct Names<'tcx> {
    names: IndexMap<(DefId, SubstsRef<'tcx>), QName>,
}

impl<'tcx> Names<'tcx> {
    pub(crate) fn get(&self, tgt: (DefId, SubstsRef<'tcx>)) -> QName {
        self.names.get(&tgt).unwrap_or_else(|| panic!("Could not find {:?}", tgt)).clone()
    }
}

pub(crate) fn name_clones<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    graph: &MonoGraph<'tcx>,
) -> Names<'tcx> {
    let mut names = IndexMap::new();
    let mut assigned = IndexMap::new();
    for node in graph.graph.nodes() {
        let Dependency::Item(def_id, subst) = node else { continue };

        let count = assigned.entry(def_id).or_insert(0);

        let base_sym = match util::item_type(ctx.tcx, def_id) {
            ItemType::Impl => ctx.tcx.item_name(ctx.tcx.trait_id_of_impl(def_id).unwrap()),
            ItemType::Closure => Symbol::intern(&format!(
                "closure{}",
                ctx.tcx.def_path(def_id).data.last().unwrap().disambiguator
            )),
            _ => ctx.tcx.item_name(def_id),
        };
        names.insert(
            (def_id, subst),
            QName {
                module: vec![format!("{}{}", base_sym.as_str().to_camel_case(), count).into()],
                name: item_name(ctx.tcx, def_id, Namespace::ValueNS),
            },
        );
    }
    Names { names }
}

// Temporary, eventually provided via a cached query
// A map of the public clones in each definition
pub struct PriorClones<'tcx> {
    prior: IndexMap<DefId, IndexMap<(DefId, SubstsRef<'tcx>), QName>>,
}

impl<'tcx> PriorClones<'tcx> {
    pub(crate) fn from_deps(ctx: &TranslationCtx<'tcx>) -> Self {
        let mut prior = IndexMap::new();

        for (id, summ) in &ctx.dependencies {
            let mut clones = IndexMap::new();
            for (k, info) in summ {
                clones.insert(*k, info.qname(ctx.tcx, k.0));
            }
            prior.insert(*id, clones);
        }

        PriorClones { prior }
    }

    pub(crate) fn get(&self, inside: DefId, tgt: (DefId, SubstsRef<'tcx>)) -> QName {
        self.prior
            .get(&inside)
            .and_then(|c| c.get(&tgt))
            .map(|q| q.clone())
            .unwrap_or_else(|| QName::from_string("INVALID.prior").unwrap())
    }
}

// Transform a graph into a set of clones
pub fn make_clones<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    graph: MonoGraph<'tcx>,
    priors: &PriorClones<'tcx>,
    level: CloneLevel,
    root: DefId,
) -> Vec<Decl> {
    let root = Dependency::Item(root, InternalSubsts::identity_for_item(ctx.tcx, root));
    let mut topo = DfsPostOrder::new(&graph.graph, root);

    let names = &name_clones(ctx, &graph);

    let desired_dep_level = match level {
        CloneLevel::Stub => DepLevel::Body, // Stub clones need a separate, shallow traversal of the graph
        CloneLevel::Interface => DepLevel::Signature,
        CloneLevel::Body => DepLevel::Body,
    };

    let mut clones = Vec::new();
    let mut uses = Vec::new();

    while let Some(node) = topo.walk_next(&graph.graph) {
        if node == root {
            continue;
        }
        if graph.level[&node] < desired_dep_level {
            continue;
        };
        eprintln!("cloning {node:?} at level {:?}", graph.level[&node]);

        let Dependency::Item(id, subst) = node else {continue };

        if item_type(ctx.tcx, id) == ItemType::Type {
            let name = item_qname(ctx, id, Namespace::TypeNS).module_qname();
            uses.push(Decl::UseDecl(Use { name: name.clone(), as_: Some(name) }));
            continue;
        };

        let mut clone_subst = base_subst(ctx, names, id, subst);

        for dep in graph.graph.neighbors_directed(node, Outgoing) {
            let (_, orig) = graph.graph[(node, dep)];
            if graph.level[&dep] < desired_dep_level {
                continue;
            };

            let Dependency::Item(id, subst) = dep else {continue };
            let orig = orig.unwrap();
            // FIXME: Not really correct
            if item_type(ctx.tcx, orig.0) == ItemType::Type {
                continue;
            }

            clone_subst.push(CloneSubst::Val(priors.get(id, orig), names.get((id, subst))))
        }

        let clone = DeclClone {
            name: cloneable_name(ctx, id, level),
            subst: clone_subst,
            kind: CloneKind::Named(names.get((id, subst)).module_ident().unwrap().clone()),
        };
        clones.push(Decl::Clone(clone));
    }

    uses.into_iter().chain(clones).collect()
}

pub fn base_subst<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &Names<'tcx>,
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
            let ty = super::ty::translate_ty(ctx, names, DUMMY_SP, ty.expect_ty());
            clone_subst.push(CloneSubst::Type(p.name.to_string().to_snake_case().into(), ty));
        }
    }

    clone_subst
}

// Which kind of module should we clone
// TODO: Unify with `CloneOpacity`
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum CloneLevel {
    Stub,
    Interface,
    Body,
}

fn cloneable_name(ctx: &TranslationCtx, def_id: DefId, interface: CloneLevel) -> QName {
    use util::ItemType::*;

    // TODO: Refactor.
    match util::item_type(ctx.tcx, def_id) {
        Logic | Predicate | Impl => match interface {
            CloneLevel::Stub => QName {
                module: Vec::new(),
                name: format!("{}_Stub", &*module_name(ctx, def_id)).into(),
            },
            CloneLevel::Interface => interface::interface_name(ctx, def_id).into(),
            CloneLevel::Body => module_name(ctx, def_id).into(),
        },
        Program | Closure => {
            QName { module: Vec::new(), name: interface::interface_name(ctx, def_id) }
        }
        Constant | Trait | Type | AssocTy => module_name(ctx, def_id).into(),
        Unsupported(_) => unreachable!(),
    }
}
