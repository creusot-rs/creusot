use rustc_mir::dataflow::impls::MaybeInitializedLocals;
use rustc_mir::dataflow::impls::MaybeLiveLocals;
use rustc_mir::dataflow::Analysis;

use rustc_middle::{mir::traversal::preorder, mir::Body, ty::TyCtxt};

use crate::polonius::PoloniusInfo;

pub fn debug<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, pol: PoloniusInfo) {
    let mut init = MaybeInitializedLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut live =
        MaybeLiveLocals.into_engine(tcx, body).iterate_to_fixpoint().into_results_cursor(body);

    let mut live2 =
        MaybeLiveLocals.into_engine(tcx, body).iterate_to_fixpoint().into_results_cursor(body);
    for (bb, bbd) in preorder(body) {
        if bbd.is_cleanup {
            continue;
        }
        println!("{:?}", bb);
        let mut loc = bb.start_location();
        for statement in &bbd.statements {
            init.seek_after_primary_effect(loc);
            live.seek_after_primary_effect(loc);
            live2.seek_before_primary_effect(loc);
            println!(
                "{:<45} init={:?} live={:?} - {:?} dying={:?}",
                format!("{:?}", statement),
                init.get(),
                live.get(),
                live2.get(),
                pol.loans_dying_at_start(loc)
            );
            loc = loc.successor_within_block();
        }
        println!(
            "{:<45} init={:?} live={:?} - {:?} dying={:?}\n",
            format!("{:?}", bbd.terminator().kind),
            init.get(),
            live.get(),
            live2.get(),
            pol.loans_dying_at_start(loc)
        );
    }
}
