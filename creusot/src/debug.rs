use rustc_mir::dataflow::impls::MaybeInitializedLocals;
use rustc_mir::dataflow::Analysis;

use rustc_middle::{mir::traversal::preorder, mir::Body, ty::TyCtxt};

use crate::polonius::PoloniusInfo;

pub fn debug<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, pol: PoloniusInfo) {
    let mut res = MaybeInitializedLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    for (bb, bbd) in preorder(body) {
        if bbd.is_cleanup {
            continue;
        }
        println!("{:?}", bb);
        let mut loc = bb.start_location();
        for statement in &bbd.statements {
            res.seek_after_primary_effect(loc);
            println!(
                "{:<45} init={:?} live={:?} dying={:?}",
                format!("{:?}", statement),
                res.get(),
                pol.loans_live_here(loc),
                pol.loans_dying_at_start(loc)
            );
            loc = loc.successor_within_block();
        }
        println!(
            "{:<45} init={:?} live={:?} dying={:?}\n",
            format!("{:?}", bbd.terminator().kind),
            res.get(),
            pol.loans_live_here(loc),
            pol.loans_dying_at_start(loc)
        );
    }
}
