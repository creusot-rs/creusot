use crate::translation::fmir::{self, Block, Branches, Terminator};
use indexmap::IndexMap;
use rustc_middle::mir::BasicBlock;

fn get_goto_block(b: &Block) -> Option<BasicBlock> {
    match b {
        // do it like this so we don't forget fields
        Block { invariants, variant, stmts, terminator: Terminator::Goto(bb) }
            if stmts.is_empty() && invariants.is_empty() && variant.is_none() =>
        {
            Some(*bb)
        }
        _ => None,
    }
}

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
    let mut shortcuts_to = IndexMap::new();
    for (&bb, block) in body.blocks.iter() {
        if let Some(to_bb) = get_goto_block(block) {
            shortcuts_to.insert(bb, to_bb);
        }
    }

    let mut replace_bb = |bb2: &mut _| find_shortcut(&mut shortcuts_to, bb2);
    for (_, block) in body.blocks.iter_mut() {
        match &mut block.terminator {
            Terminator::Goto(bb) => replace_bb(bb),
            Terminator::Switch(_, branches) => match branches {
                Branches::Int(items, def) => {
                    replace_bb(def);
                    for (_, to) in items {
                        replace_bb(to);
                    }
                }
                Branches::Uint(items, def) => {
                    replace_bb(def);
                    for (_, to) in items {
                        replace_bb(to);
                    }
                }
                Branches::Constructor(_, _, cases, def) => {
                    if let Some(def) = def {
                        replace_bb(def);
                    }
                    for (_, to) in cases {
                        replace_bb(to);
                    }
                }
                Branches::Bool(to1, to2) => {
                    replace_bb(to1);
                    replace_bb(to2);
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
fn find_shortcut(shortcuts: &mut IndexMap<BasicBlock, BasicBlock>, from: &mut BasicBlock) {
    // We remove the shortcut to avoid looping in the case of loops.
    let Some(mut to) = shortcuts.swap_remove(from) else { return };
    find_shortcut(shortcuts, &mut to);
    if to != *from {
        shortcuts.insert(*from, to); // Compress path
        *from = to
    }
}
