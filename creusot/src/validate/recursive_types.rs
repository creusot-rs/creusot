use crate::{
    backend::ty::classify_adt,
    contracts_items::{get_creusot_item, is_opaque, is_trusted, is_trusted_terminates},
    ctx::{HasTyCtxt as _, TranslationCtx},
    validate::terminates::{find_path, proof_tree_nodes},
};
use petgraph::{algo::tarjan_scc, graph};
use rustc_hir::def_id::DefId;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::ty::{self, AliasTyKind, AssocKind, EarlyBinder, Unnormalized};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};

pub fn validate_recursive_types(ctx: &TranslationCtx) {
    let graph = build_type_graph(ctx);
    let mut positivity = StrictPositivity::new();

    for scc in tarjan_scc(&graph.graph) {
        // Not a cycle: SCC with a single node and no self edge
        if scc.len() == 1
            && let node = scc[0]
            && graph.graph.find_edge(node, node).is_none()
        {
            continue;
        }
        let in_scc: HashSet<_> = scc.iter().cloned().collect();
        let Err((node, (err, recnode))) = scc.iter().try_for_each(|&node| {
            check_recursion(ctx, &mut positivity, &graph, &in_scc, node).map_err(|err| (node, err))
        }) else {
            continue;
        };
        let node_label = graph.graph[node];
        let span = ctx.def_span(node_label.did());
        let recnode_name = ctx.def_path_str(graph.graph[recnode].did());
        use IllegalRecursion::*;
        let mut error = match err {
            RecursiveTrait => ctx.error(span, "Illegal recursive trait"),
            RecursiveAssocType => ctx.error(span, "Illegal recursive associated type"),
            NotStrictlyPositive(field_span, forbidder) => {
                let mut error = ctx.error(span, "Illegal recursive type");
                let forbidder = forbidder.display(ctx);
                error.span_label(
                    field_span,
                    format!("Recursive occurrence of {recnode_name} under {forbidder}"),
                );
                error
            }
        };
        let cycle = find_path(&graph.graph, &in_scc, recnode, node);
        let cycle_len = cycle.len();
        let mut current = recnode;
        let mut current_name = recnode_name;
        for next in cycle.iter().cloned() {
            let next_name = ctx.def_path_str(graph.graph[next].did());
            use TypeEdge::*;
            match graph.graph[graph.graph.find_edge(current, next).unwrap()] {
                // Trivial cycle
                AdtDef(_) | Supertrait(_) if cycle_len == 1 => {}
                AdtDef(span) => {
                    error.span_note(
                        span,
                        format!("`{next_name}` occurs in this field of `{current_name}`"),
                    );
                }
                AdtDefBound(span, middle) => {
                    let middle = ctx.def_path_str(middle);
                    error.span_note(
                        span,
                        format!("`{next_name}` is used in this field of `{current_name}`, when resolving a bound of `{middle}`"),
                    );
                }
                AssocType(assoc_id) => {
                    let assoc = ctx.def_path_str(assoc_id);
                    error.span_note(
                        ctx.def_span(assoc_id),
                        format!("`{next_name}` occurs in the definition of `{assoc}`"),
                    );
                }
                Supertrait(span) => {
                    error.span_note(
                        span,
                        format!("`{next_name}` is a supertrait of `{current_name}`"),
                    );
                }
                FnBound(method, span) => {
                    let meth = ctx.def_path_str(method);
                    error.span_note(span, format!("`{next_name}` is a bound of `{meth}`"));
                }
            }
            current = next;
            current_name = next_name;
        }
        error.emit();
    }
}

enum IllegalRecursion {
    RecursiveTrait,
    RecursiveAssocType,
    NotStrictlyPositive(Span, ForbidsRecursion),
}

enum ForbidsRecursion {
    Abstract(DefId),
    NotStrictlyPositive(DefId, usize),
    Impl(DefId),
    Assoc(DefId),
    Other(String),
}

impl ForbidsRecursion {
    fn display(self, ctx: &TranslationCtx) -> String {
        use ForbidsRecursion::*;
        match self {
            Abstract(def_id) => format!("abstract type `{}`", ctx.def_path_str(def_id)),
            NotStrictlyPositive(def_id, index) => {
                format!("parameter {index} of type `{}`", ctx.def_path_str(def_id))
            }
            Impl(impl_id) => format!("trait bound using `{}`", ctx.def_path_str(impl_id)),
            Assoc(def_id) => format!("associated type `{}`", ctx.def_path_str(def_id)),
            Other(desc) => desc,
        }
    }
}

/// Return `Err` if illegal recursion is found, with span that locates the problem.
fn check_recursion(
    ctx: &TranslationCtx,
    positivity: &mut StrictPositivity,
    graph: &TypeGraph,
    scc: &HashSet<graph::NodeIndex>,
    node: graph::NodeIndex,
) -> Result<(), (IllegalRecursion, graph::NodeIndex)> {
    use IllegalRecursion::*;
    use TypeNode::*;
    match graph.graph[node] {
        Trait(_) => Err((RecursiveTrait, node)),
        Type(type_id) => walk_adt(ctx, type_id, |tgt, path, span| {
            let index = graph.node_map[&tgt];
            if scc.contains(&index) {
                use TypeNode::*;
                match tgt {
                    Type(_) => forbid_recursion(ctx, positivity, type_id, path),
                    TraitImpl(impl_id) => Err(ForbidsRecursion::Impl(impl_id)),
                    Trait(_) => unreachable!(),
                }
                .map_err(|e| (NotStrictlyPositive(span, e), index))
            } else {
                Ok(())
            }
        }),
        TraitImpl(_) => Err((RecursiveAssocType, node)),
    }
}

/// Check whether the given `path` forbids recursion,
/// using visibility relative to `type_id`.
fn forbid_recursion<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    positivity: &mut StrictPositivity,
    type_id: DefId,
    path: &[(ty::Ty<'tcx>, Option<usize>)],
) -> Result<(), ForbidsRecursion> {
    use ForbidsRecursion::*;
    use rustc_type_ir::TyKind::*;
    path.iter().try_for_each(|(ty, index)| match ty.kind() {
        &Adt(def, subst) => {
            use crate::backend::ty::AdtKind::*;
            match classify_adt(ctx, type_id, def, subst) {
                Opaque { .. } | Struct { partially_opaque: true } | Builtin(_) => {
                    if ctx.trusted_positivity(def.did(), index.unwrap()) {
                        Ok(())
                    } else {
                        Err(Abstract(def.did()))
                    }
                }
                Unit | Empty | Snapshot(_) | Box(_) | Identity(_) => Ok(()),
                Enum | Struct { partially_opaque: false } => {
                    let index = index.unwrap();
                    if positivity.get(ctx, def.did(), index) {
                        Ok(())
                    } else {
                        Err(NotStrictlyPositive(def.did(), index))
                    }
                }
                Namespace => unreachable!(),
            }
        }
        // recursion through arrays and slices is not yet supported
        Array(_, _) => Err(Other("array".into())),
        Slice(_) => Err(Other("slice".into())),
        Alias(alias) => {
            let (AliasTyKind::Projection { def_id }
            | AliasTyKind::Inherent { def_id }
            | AliasTyKind::Opaque { def_id }
            | AliasTyKind::Free { def_id }) = alias.kind;
            Err(Assoc(def_id))
        }
        _ => Ok(()),
    })
}

/// Map each ADT to a vector indicating the "strict positivity" of its arguments.
///
/// That an ADT `W<X, Y>` is strictly positive in its first argument (`X`),
/// whatever that means, must imply that it can contain a recursive occurrence of a type.
///
/// ```ignored
/// // Valid if `W` is strictly positive in its first argument
/// struct A(W<A, ()>);
/// ```
struct StrictPositivity {
    positivity: HashMap<DefId, DenseBitSet<usize>>,
}

impl StrictPositivity {
    fn new() -> Self {
        Self { positivity: HashMap::new() }
    }

    fn get(&mut self, ctx: &TranslationCtx, def_id: DefId, index: usize) -> bool {
        self.positivity
            .entry(def_id)
            .or_insert_with(|| {
                ctx.get_trusted_positivity(def_id)
                    .map(|tp| tp.positivity.clone())
                    .unwrap_or_else(|| get_positivity(ctx, def_id))
            })
            .contains(index)
    }
}

fn get_positivity(ctx: &TranslationCtx, def_id: DefId) -> DenseBitSet<usize> {
    struct ArgPositivity(DenseBitSet<usize>);

    use rustc_type_ir::TyKind::Param;
    use ty::{TypeSuperVisitable as _, TypeVisitor};
    impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for ArgPositivity {
        type Result = ();

        fn visit_ty(&mut self, t: ty::Ty) {
            use rustc_type_ir::inherent::ParamLike as _;
            match t.kind() {
                &Param(param) => {
                    let index = param.index() as usize;
                    self.0.remove(index);
                }
                _ => t.super_visit_with(self),
            }
        }
    }

    let generics = ctx.generics_of(def_id);
    let mut positivity = ArgPositivity(DenseBitSet::new_filled(generics.count()));
    for field in ctx.adt_def(def_id).variants().iter().flat_map(|vdef| vdef.fields.iter()) {
        let mut ty = ctx.type_of(field.did).instantiate_identity().skip_normalization();
        // "Strictly positive" parameters are those that appear only naked or under `Box`,
        // `Ghost`, `Snapshot`, and `&`.
        // FIXME: allow nesting under other "strictly positive" types
        loop {
            use crate::backend::ty::AdtKind as K;
            use rustc_type_ir::TyKind::*;
            match ty.kind() {
                &Adt(def, args)
                    if let K::Box(arg) | K::Snapshot(arg) =
                        classify_adt(ctx, def_id, def, args) =>
                {
                    ty = arg
                }
                &Ref(_, arg, _) => ty = arg,
                Param(_) => break,
                _ => {
                    // Mark all parameters that appear here as not strictly positive
                    positivity.visit_ty(ty);
                    break;
                }
            }
        }
    }
    positivity.0
}

/// Graph of types and traits
struct TypeGraph {
    node_map: HashMap<TypeNode, graph::NodeIndex>,
    graph: graph::DiGraph<TypeNode, TypeEdge>,
}

impl TypeGraph {
    fn new() -> Self {
        Self { node_map: HashMap::new(), graph: graph::DiGraph::new() }
    }

    fn node(&mut self, node: TypeNode) -> graph::NodeIndex {
        *self.node_map.entry(node).or_insert_with(|| self.graph.add_node(node))
    }

    fn add_edge(&mut self, source: graph::NodeIndex, target: TypeNode, edge: TypeEdge) {
        let target = self.node(target);
        if let None = self.graph.find_edge(source, target) {
            self.graph.add_edge(source, target, edge);
        }
    }
}

/// Nodes for `TypeGraph`
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum TypeNode {
    Type(DefId),
    Trait(DefId),
    /// Types may depend on trait impls for their associated types
    TraitImpl(DefId),
}

impl TypeNode {
    fn did(self) -> DefId {
        use TypeNode::*;
        match self {
            Type(did) | Trait(did) | TraitImpl(did) => did,
        }
    }
}

/// Edges for `TypeGraph`
/// Metainformation about the kind of dependency this edge represents.
#[derive(Debug)]
enum TypeEdge {
    AdtDef(Span),
    /// The target impl was used when instantiating the ADT given by `DefId`.
    AdtDefBound(Span, DefId),
    /// The target type occurs in an associated type of the source trait impl
    AssocType(DefId),
    /// A trait mentions another trait in its supertraits
    Supertrait(Span),
    /// A trait mentions another trait in the signature of a method.
    FnBound(DefId, Span),
}

fn build_type_graph(ctx: &TranslationCtx) -> TypeGraph {
    let mut graph = TypeGraph::new();

    for id in ctx.hir_free_items() {
        let item = ctx.hir_item(id);
        use rustc_hir::ItemKind::*;
        match item.kind {
            Struct(..) | Enum(..) | Union(..) => {
                add_type(ctx, item.owner_id.to_def_id(), &mut graph)
            }
            Trait(..) => add_trait(ctx, item.owner_id.to_def_id(), &mut graph),
            _ => {}
        }
    }

    // Add an edge from every trait impl to types that occur in its associated type definitions.
    for (&_trait_id, impls) in ctx.all_local_trait_impls(()) {
        for &impl_id in impls {
            add_trait_impl(ctx, impl_id.to_def_id(), &mut graph);
        }
    }

    graph
}

fn add_type(ctx: &TranslationCtx, def_id: DefId, graph: &mut TypeGraph) {
    if is_opaque(ctx.tcx, def_id)
        || is_trusted(ctx.tcx, def_id)
        || is_trusted_terminates(ctx.tcx, def_id)
    {
        return;
    }
    let node = graph.node(TypeNode::Type(def_id));
    walk_adt(ctx, def_id, |tgt, path, span| {
        let edge = if let TypeNode::TraitImpl(_) = tgt {
            let ty::TyKind::Adt(adt, _) = path.last().unwrap().0.kind() else { unreachable!() };
            TypeEdge::AdtDefBound(span, adt.did())
        } else {
            TypeEdge::AdtDef(span)
        };
        Ok::<(), !>(graph.add_edge(node, tgt, edge))
    })
    .unwrap()
}

fn add_trait(ctx: &TranslationCtx, def_id: DefId, graph: &mut TypeGraph) {
    if is_trusted(ctx.tcx, def_id) {
        return;
    }
    let node = graph.node(TypeNode::Trait(def_id));

    for &(clause, span) in
        ctx.trait_explicit_predicates_and_bounds(def_id.expect_local()).predicates
    {
        if let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
            graph.add_edge(
                node,
                TypeNode::Trait(predicate.trait_ref.def_id),
                TypeEdge::Supertrait(span),
            );
        }
    }

    for item in ctx.associated_items(def_id).in_definition_order() {
        if get_creusot_item(ctx.tcx, item.def_id).is_some() {
            // Skip fake methods
            continue;
        }
        for &(clause, span) in ctx.predicates_of(item.def_id.expect_local()).predicates {
            if let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() {
                graph.add_edge(
                    node,
                    TypeNode::Trait(predicate.trait_ref.def_id),
                    TypeEdge::FnBound(item.def_id, span),
                );
            }
        }
    }
}

fn add_trait_impl(ctx: &TranslationCtx, def_id: DefId, graph: &mut TypeGraph) {
    let node = graph.node(TypeNode::TraitImpl(def_id));
    for &item in ctx.associated_items(def_id).in_definition_order() {
        if let AssocKind::Type { .. } = item.kind {
            let typing_env = ctx.typing_env(item.def_id);
            let ty = ctx.normalize_erasing_regions(
                typing_env,
                Unnormalized::new(ctx.type_of(item.def_id).skip_binder()),
            );
            let mut path = Vec::new();
            walk_type(ctx, typing_env, ty, &mut path, &mut |tgt, _| {
                Ok::<(), !>(graph.add_edge(node, tgt, TypeEdge::AssocType(item.def_id)))
            });
        }
    }
}

fn walk_adt<'tcx, E>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    mut f: impl for<'a> FnMut(TypeNode, &'a [(ty::Ty<'tcx>, Option<usize>)], Span) -> Result<(), E>,
) -> Result<(), E> {
    let def = ctx.adt_def(def_id);
    let typing_env = ctx.typing_env(def.did());
    let mut path = Vec::new();
    for fdef in def.variants().iter().flat_map(|vdef| vdef.fields.iter()) {
        let span = ctx.def_span(fdef.did);
        let field_ty =
            ctx.normalize_erasing_regions(typing_env, ctx.type_of(fdef.did).instantiate_identity());
        walk_type(ctx, typing_env, field_ty, &mut path, &mut |tgt, path| f(tgt, path, span))?;
        assert! { path.is_empty() };
    }
    Ok(())
}

/// Find all type constructors and trait impls that occur in `ty` (must be normalized).
///
/// Accumulate a `path` of types from the root to the current subterm
/// (with an optional index of the type argument of an ADT).
/// Primitive types that always allow recursion are omitted from the `path`: `&`, `Box`, tuples.
///
/// This path is ignored in `add_type`, but used for checking recursive occurrences in `check_recursion`.
fn walk_type<'tcx, E>(
    ctx: &TranslationCtx<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: ty::Ty<'tcx>,
    path: &mut Vec<(ty::Ty<'tcx>, Option<usize>)>,
    f: &mut impl for<'a> FnMut(TypeNode, &'a [(ty::Ty<'tcx>, Option<usize>)]) -> Result<(), E>,
) -> Result<(), E> {
    use rustc_type_ir::TyKind::*;
    match ty.kind() {
        &Adt(adt, args) => {
            f(TypeNode::Type(adt.did()), path)?;
            // Add edges to impls used to resolve bounds on this ADT's generic arguments
            let clauses = ctx.predicates_of(adt.did()).predicates.iter().map(|&(clause, _)| {
                ctx.normalize_erasing_regions(
                    typing_env,
                    EarlyBinder::bind(clause).instantiate(ctx.tcx, args),
                )
            });
            path.push((ty, None)); // Pass the current type to f (for more precise errors)
            for trait_impl in proof_tree_nodes(ctx.tcx, typing_env, clauses) {
                f(TypeNode::TraitImpl(trait_impl), path)?;
            }
            path.pop();
            // Iterate through all arguments to get the right indices
            args.iter().enumerate().try_for_each(|(index, arg)| {
                let Some(arg) = arg.as_type() else { return Ok(()) };
                path.push((ty, Some(index)));
                walk_type(ctx, typing_env, arg, path, f)?;
                path.pop();
                Ok(())
            })?;
        }
        &Array(arg, _) | &Slice(arg) => {
            path.push((ty, None));
            walk_type(ctx, typing_env, arg, path, f)?;
            path.pop();
        }
        &Ref(_, arg, _) => walk_type(ctx, typing_env, arg, path, f)?,
        &Tuple(args) => {
            args.iter().try_for_each(|arg| walk_type(ctx, typing_env, arg, path, f))?;
        }
        Alias(alias) => {
            // Types are normalized, so the only case left should be unresolved associated types.
            // FIXME: Figure out how to handle this properly.
            path.push((ty, None));
            alias.args.types().try_for_each(|arg| walk_type(ctx, typing_env, arg, path, f))?;
            path.pop();
        }
        &Dynamic(_predicates, _) => {
            // FIXME: Handle this
        }
        _ => {}
    }
    Ok(())
}
