use petgraph::{
    Direction,
    visit::{GraphBase, IntoNeighborsDirected, Visitable},
};
use std::{collections::HashMap, hash::Hash};

/// Domination information of the graph.
///
/// Those will be used to reconstruct loops.
#[derive(Debug, Clone)]
pub enum Component<N> {
    Vertex(N),
    /// Every vertex in the second part is _dominated_ by the first.
    ///
    /// That is, in order to go to a vertex in the second part, you _have_ to
    /// go through the first part (given a starting vertex).
    Component(N, Vec<Component<N>>),
}

/// Returns domination information of the graph `G`.
pub fn weak_topological_order<G>(g: G, root: G::NodeId) -> Vec<Component<G::NodeId>>
where
    G: IntoNeighborsDirected + Visitable,
    <G as GraphBase>::NodeId: Eq + Hash,
{
    let mut wto = Wto { stack: Vec::new(), graph: g, num: 0, dfn: HashMap::new() };
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
        if state.dfn.get(&s).unwrap_or(&0) == &0 {
            visit(state, s, &mut component);
        }
    }

    component.reverse();
    Component::Component(v, component)
}

struct Wto<G: GraphBase> {
    stack: Vec<G::NodeId>,
    graph: G,
    num: u32,
    /// Maps the vertex to an index.
    /// - If the index is 0, the vertex should be visited.
    /// - If the index is u32::MAX, ??
    /// - Else if the index is i, the vertex is the i-th vertex to be visited.
    dfn: HashMap<G::NodeId, u32>,
}

fn visit<G>(state: &mut Wto<G>, v: G::NodeId, partition: &mut Vec<Component<G::NodeId>>) -> u32
where
    G: IntoNeighborsDirected + Visitable,
    <G as GraphBase>::NodeId: Eq + Hash,
{
    state.stack.push(v);
    state.num += 1;
    let v_dfn = state.num;
    state.dfn.insert(v, v_dfn);

    let mut head = v_dfn;
    let mut loop_ = false;
    for s in state.graph.neighbors_directed(v, Direction::Outgoing) {
        let min = if state.dfn.get(&s).is_none_or(|&n| n == 0) {
            visit(state, s, partition)
        } else {
            state.dfn[&s]
        };

        if min <= head {
            head = min;
            loop_ = true;
        }
    }

    if head == *state.dfn.get(&v).unwrap() {
        state.dfn.insert(v, u32::MAX);
        let mut element = state.stack.pop().unwrap();

        if loop_ {
            while element != v {
                state.dfn.insert(element, 0);
                element = state.stack.pop().unwrap();
            }
            partition.push(component(state, v));
        } else {
            partition.push(Component::Vertex(v));
        }
    }

    head
}
