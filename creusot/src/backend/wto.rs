use petgraph::{
    Direction,
    visit::{GraphBase, IntoNeighborsDirected, Visitable},
};
use std::{
    collections::{HashMap, hash_map::Entry},
    hash::Hash,
};

/// Domination information of the graph.
///
/// Those will be used to reconstruct loops.
#[derive(Debug, Clone)]
pub enum Component<N> {
    /// In the `Simple` case, we are guaranteed the vertex have no self-loop
    Simple(N),
    /// Every vertex in the second part is _dominated_ by the first.
    ///
    /// That is, in order to go to a vertex in the second part, you _have_ to
    /// go through the first part (given a starting vertex).
    ///
    /// In addition, the second part is topologically sorted
    Complex(N, Vec<Component<N>>),
}

/// Returns domination information of the graph `G`.
pub fn weak_topological_order<G>(graph: G, root: G::NodeId) -> Vec<Component<G::NodeId>>
where
    G: IntoNeighborsDirected + Visitable,
    <G as GraphBase>::NodeId: Eq + Hash,
{
    let mut wto = Wto { stack: Vec::new(), graph, num: 0, dfn: HashMap::new() };
    let mut partition = Vec::new();
    visit(&mut wto, root, &mut partition);
    partition.reverse();
    partition
}

fn component<G>(state: &mut Wto<G>, v: G::NodeId) -> Component<G::NodeId>
where
    G: IntoNeighborsDirected + Visitable,
    <G as GraphBase>::NodeId: Eq + Hash,
{
    let mut component = Vec::new();
    for s in state.graph.neighbors_directed(v, Direction::Outgoing) {
        visit(state, s, &mut component);
    }

    component.reverse();
    for c in component.iter() {
        let head = match c {
            Component::Simple(h) => h,
            Component::Complex(h, _) => h,
        };
        let Some(NodeState::Head(b @ false)) = state.dfn.get_mut(head) else { unreachable!() };
        *b = true
    }
    Component::Complex(v, component)
}

#[derive(Clone, Copy)]
enum NodeState {
    /// The integer is the date of the start of the visit
    CurrentlyVisited(u32),
    /// Head of a component: the Boolean indicates whether it is dominated by a completed component
    Head(bool),
}

struct Wto<G: GraphBase> {
    stack: Vec<G::NodeId>,
    graph: G,
    num: u32,

    /// Maps the vertex to an index.
    /// - If None, the vertex should be visited.
    /// - If the index is u32::MAX, the vertex has been visited
    /// - Else if the index is i, the vertex is being visited, and the value indicates the date of
    ///   start of visit.
    dfn: HashMap<G::NodeId, NodeState>,
}

fn visit<G>(state: &mut Wto<G>, v: G::NodeId, partition: &mut Vec<Component<G::NodeId>>) -> u32
where
    G: IntoNeighborsDirected + Visitable,
    <G as GraphBase>::NodeId: Eq + Hash,
{
    let e = match state.dfn.entry(v) {
        Entry::Occupied(e) => match e.get() {
            NodeState::CurrentlyVisited(r) => return *r,
            NodeState::Head(false) => return u32::MAX,
            NodeState::Head(true) => unreachable!("Unreducible graph."),
        },
        Entry::Vacant(e) => e,
    };

    state.stack.push(v);
    state.num += 1;
    let v_dfn = state.num;
    e.insert(NodeState::CurrentlyVisited(v_dfn));

    let mut head = v_dfn;
    let mut loop_ = false;
    for s in state.graph.neighbors_directed(v, Direction::Outgoing) {
        let min = visit(state, s, partition);
        if min <= head {
            head = min;
            loop_ = true;
        }
    }

    if head == v_dfn {
        // Back edges do not go higher than us: we are at the head of a component.
        // ==> Restart the traversal to build sub-components
        state.dfn.insert(v, NodeState::Head(false));
        for e in std::iter::from_fn(|| state.stack.pop()).take_while(|e| *e != v) {
            assert!(loop_);
            state.dfn.remove(&e);
        }
        if loop_ {
            partition.push(component(state, v));
        } else {
            partition.push(Component::Simple(v));
        }
    }

    head
}
