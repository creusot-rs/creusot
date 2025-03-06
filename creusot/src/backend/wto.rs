use std::{collections::HashMap, hash::Hash};

use petgraph::{
    Direction,
    visit::{GraphBase, IntoNeighborsDirected, Visitable},
};

#[derive(Debug, Clone)]
pub enum Component<N> {
    Vertex(N),
    Component(N, Vec<Component<N>>),
}

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
    return Component::Component(v, component);
}

struct Wto<G: GraphBase> {
    stack: Vec<G::NodeId>,
    graph: G,
    num: u32,
    dfn: HashMap<G::NodeId, u32>,
}

fn visit<G>(state: &mut Wto<G>, v: G::NodeId, partition: &mut Vec<Component<G::NodeId>>) -> u32
where
    G: IntoNeighborsDirected + Visitable,
    <G as GraphBase>::NodeId: Eq + Hash,
{
    state.stack.push(v);
    state.num += 1;
    state.dfn.insert(v, state.num);

    let mut head = state.dfn[&v];
    let mut loop_ = false;

    for s in state.graph.neighbors_directed(v, Direction::Outgoing) {
        let min = if *state.dfn.get(&s).unwrap_or(&0) == 0 {
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

    return head;
}
