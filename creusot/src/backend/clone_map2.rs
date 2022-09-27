use std::collections::HashSet;

use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{
        subst::{Subst, SubstsRef},
        EarlyBinder,
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
use rustc_middle::ty::{subst::InternalSubsts, DefIdTree, TyCtxt, TyKind};
use util::ItemType;
use why3::{
    declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use},
    ty::Type,
    Print, QName,
};

use crate::{
    clone_map::CloneSummary,
    ctx::TranslationCtx,
    translation::traits::resolve_opt,
    util::{self, item_name, item_qname, item_type},
};

// The clone wars are over
// Implements a simpler version of CloneMap, split as two operations: gathering all the 'monomorphic' instances of functions / types used
// and a second why3 specific pass turning that into clones (and later not into clones!)
//

// Temporary to start testing
fn get_immediate_deps<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DefId, SubstsRef<'tcx>)> {
    match item_type(ctx.tcx, def_id) {
        ItemType::Type => {
            let substs = InternalSubsts::identity_for_item(ctx.tcx, def_id);
            let tys = ctx
                .adt_def(def_id)
                .all_fields()
                .map(|f| f.ty(ctx.tcx, substs))
                .flat_map(|fld| fld.walk());

            let mut v = Vec::new();

            for ty in tys {
                match ty.expect_ty().kind() {
                    TyKind::Adt(def, sub) => v.push((def.did(), *sub)),
                    _ => {}
                }
            }
            v
        }
        _ => ctx.dependencies(def_id).map(|i| i.keys().cloned().collect()).unwrap_or_default(),
    }
}

type MonoGraph<'tcx> = DiGraphMap<(DefId, SubstsRef<'tcx>), (DefId, SubstsRef<'tcx>)>;

pub fn collect<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> MonoGraph<'tcx> {
    let mut to_visit = vec![(def_id, InternalSubsts::identity_for_item(ctx.tcx, def_id))];
    let mut finished = HashSet::new();
    let param_env = ctx.param_env(def_id);

    let mut graph = MonoGraph::default();
    while let Some(next) = to_visit.pop() {
        if !finished.insert(next) {
            // Already visited
            continue;
        }
        graph.add_node(next);

        let to_add = EarlyBinder(get_immediate_deps(ctx, next.0)).subst(ctx.tcx, next.1);

        for dep in to_add {
            let tgt = if can_resolve(ctx, dep) {
                resolve_opt(ctx.tcx, param_env, dep.0, dep.1).unwrap()
            } else {
                ctx.normalize_erasing_regions(param_env, dep)
            };

            graph.add_edge(next, tgt, dep);

            to_visit.push(tgt);
        }
    }

    // let prior = PriorClones::from_deps(ctx.tcx, &ctx.dependencies);

    // make_clones(ctx, graph.clone(), &prior, def_id);
    graph
}

fn can_resolve<'tcx>(ctx: &mut TranslationCtx<'tcx>, dep: (DefId, SubstsRef<'tcx>)) -> bool {
    ctx.trait_of_item(dep.0).is_some()
}

pub struct Names<'tcx> {
    names: IndexMap<(DefId, SubstsRef<'tcx>), QName>,
}

impl<'tcx> Names<'tcx> {
    pub(crate) fn get(&self, tgt: (DefId, SubstsRef<'tcx>)) -> QName {
        self.names.get(&tgt).unwrap_or_else(|| panic!("Could not find {:?}", tgt)).clone()
    }
}

pub fn name_clones<'tcx>(ctx: &mut TranslationCtx<'tcx>, graph: &MonoGraph<'tcx>) -> Names<'tcx> {
    let mut names = IndexMap::new();
    let mut assigned = IndexMap::new();
    for (def_id, subst) in graph.nodes() {
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
    root: DefId,
) -> Vec<Decl> {
    let mut topo =
        DfsPostOrder::new(&graph, (root, InternalSubsts::identity_for_item(ctx.tcx, root)));

    let names = &name_clones(ctx, &graph);

    let mut clones = Vec::new();
    let mut uses = Vec::new();

    while let Some(node) = topo.walk_next(&graph) {
        if node.0 == root {
            continue;
        }

        if item_type(ctx.tcx, node.0) == ItemType::Type {
            let name = item_qname(ctx, node.0, Namespace::TypeNS).module_qname();
            uses.push(Decl::UseDecl(Use { name: name.clone(), as_: Some(name) }));
            continue;
        };

        let mut subst = base_subst(ctx, names, node.0, node.1);

        for dep in graph.neighbors_directed(node, Outgoing) {
            if item_type(ctx.tcx, dep.0) == ItemType::Type {
                continue;
            }

            let orig = graph[(node, dep)];
            subst.push(CloneSubst::Val(priors.get(node.0, orig), names.get(dep)))
        }

        let clone = DeclClone { name: names.get(node), subst, kind: CloneKind::Bare };
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
