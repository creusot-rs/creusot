use crate::translation::fmir::{self, Block, Terminator};
use indexmap::{IndexMap, map::Entry};
use rustc_middle::mir::{BasicBlock, START_BLOCK};

fn is_simple_block(b: &Block) -> bool {
    if let Block {
        invariants,
        variant,
        stmts,
        terminator: Terminator::Goto(_) | Terminator::Abort(_) | Terminator::Return,
    } = b
    {
        stmts.is_empty() && invariants.is_empty() && variant.is_none()
    } else {
        false
    }
}

/// Remove:
/// - Unreachable blocks
/// - Shortcut blocks (i.e., blocks that only contain a goto)
/// - Jump to a block that only returns or aborts
/// - blocks that only have a predecessor which is a goto
///
/// These optimization should not change at all the VCs, but they make the COMA code much
/// more human-readable.
pub(super) fn remove_useless_gotos(body: &mut fmir::Body) {
    // Compute shortcuts
    let mut shortcuts_to = IndexMap::new();
    let mut short_term = IndexMap::new();
    for (&bb, block) in body.blocks.iter() {
        if is_simple_block(block) {
            match &block.terminator {
                Terminator::Goto(to_bb) => {
                    shortcuts_to.insert(bb, *to_bb);
                }
                trm => {
                    short_term.insert(bb, trm.clone());
                }
            }
        }
    }

    for (_, block) in body.blocks.iter_mut() {
        // Remove goto chains
        for tgt in block.terminator.targets_mut() {
            find_shortcut(&mut shortcuts_to, tgt)
        }

        // Remove gotos to return/abort
        if let Terminator::Goto(nxt) = block.terminator
            && let Some(term) = short_term.get(&nxt)
        {
            block.terminator = term.clone()
        }
    }

    // Remove shortcut at the first block
    let start_block = &body.blocks[&START_BLOCK];
    if is_simple_block(start_block)
        && let Terminator::Goto(new_start) = start_block.terminator
        && new_start != START_BLOCK
    {
        let [Some(b1), Some(b2)] = body.blocks.get_disjoint_mut([&START_BLOCK, &new_start]) else {
            unreachable!()
        };
        std::mem::swap(b1, b2);

        for (_, block) in body.blocks.iter_mut() {
            for tgt in block.terminator.targets_mut() {
                if *tgt == new_start {
                    *tgt = START_BLOCK
                }
            }
        }
    }

    // Count predecessors for each block
    let mut cnt_prev = IndexMap::from([(START_BLOCK, 1u32)]);
    for (_, block) in body.blocks.iter() {
        for tgt in block.terminator.targets() {
            *cnt_prev.entry(tgt).or_insert(0) += 1;
        }
    }

    // Remove orphan blocks
    let mut stk: Vec<BasicBlock> =
        body.blocks.keys().copied().filter(|bb| !cnt_prev.contains_key(bb)).collect();
    while let Some(bb) = stk.pop() {
        for tgt in body.blocks.swap_remove(&bb).unwrap().terminator.targets() {
            let Entry::Occupied(mut e) = cnt_prev.entry(tgt) else { unreachable!() };
            *e.get_mut() -= 1;
            if *e.get() == 0 {
                stk.push(tgt);
                e.swap_remove();
            }
        }
    }

    // Merge when goto to a block with only one predecessor
    for bb in body.blocks.keys().copied().collect::<Vec<_>>() {
        loop {
            let Some(&Block { terminator: Terminator::Goto(nextbb), .. }) = body.blocks.get(&bb)
            else {
                break;
            };
            if cnt_prev[&nextbb] > 1 || bb == nextbb {
                break;
            }
            let Entry::Occupied(e) = body.blocks.entry(nextbb) else { unreachable!() };
            if !e.get().invariants.is_empty() || e.get().variant.is_some() {
                break;
            }
            let Block { invariants: _, variant: _, stmts, terminator } = e.swap_remove();
            body.blocks[&bb].stmts.extend(stmts);
            body.blocks[&bb].terminator = terminator;
            assert_eq!(cnt_prev.swap_remove(&nextbb), Some(1));
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
