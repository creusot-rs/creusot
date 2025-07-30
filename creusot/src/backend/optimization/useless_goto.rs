use crate::{
    backend::program::node_graph,
    translation::fmir::{self, Terminator},
};
use indexmap::{IndexMap, IndexSet};
use rustc_middle::mir::BasicBlock;

/// Remove the common pattern:
/// ```text
/// bb1:
///     ...
///     goto bb2
/// bb2:
///     goto bb3
/// bb3:
///     ...
/// ```
/// `bb2` is useless here.
pub(super) fn remove_useless_gotos(body: &mut fmir::Body) {
    let graph = node_graph(body);

    let mut shortcuts_to = IndexMap::new();
    for bb in graph.nodes() {
        let block = &body.blocks[&bb];
        if block.stmts.is_empty()
            && block.variant.is_none()
            && block.invariants.is_empty()
            && let Terminator::Goto(to_bb) = block.terminator
        {
            shortcuts_to.insert(bb, to_bb);
        }
    }

    let mut visited = IndexSet::new();
    let mut replace_with = |bb2: &mut _| {
        visited.clear();
        if let Some(to) = find_shortcut(&mut shortcuts_to, *bb2, &mut visited) {
            *bb2 = to;
        }
    };
    for bb in graph.nodes() {
        match &mut body.blocks[&bb].terminator {
            Terminator::Goto(bb) => replace_with(bb),
            Terminator::Switch(_, branches) => match branches {
                fmir::Branches::Int(items, def) => {
                    replace_with(def);
                    for (_, to) in items {
                        replace_with(to);
                    }
                }
                fmir::Branches::Uint(items, def) => {
                    replace_with(def);
                    for (_, to) in items {
                        replace_with(to);
                    }
                }
                fmir::Branches::Constructor(_, _, cases, def) => {
                    if let Some(def) = def {
                        replace_with(def);
                    }
                    for (_, to) in cases {
                        replace_with(to);
                    }
                }
                fmir::Branches::Bool(to1, to2) => {
                    replace_with(to1);
                    replace_with(to2);
                }
            },
            Terminator::Return | Terminator::Abort(_) => {}
        }
    }
}

/// Find the block that `from` shortcuts to, compressing paths in `shortcuts`
/// as needed.
///
/// This will correctly detect loops.
fn find_shortcut(
    shortcuts: &mut IndexMap<BasicBlock, BasicBlock>,
    from: BasicBlock,
    visited: &mut IndexSet<BasicBlock>,
) -> Option<BasicBlock> {
    if !visited.insert(from) {
        return Some(from);
    }
    let to = *shortcuts.get(&from)?;
    match find_shortcut(shortcuts, to, visited) {
        Some(next) => {
            shortcuts.insert(from, next);
            Some(next)
        }
        None => Some(to),
    }
}
