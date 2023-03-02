use rustc_mir_dataflow::impls::{MaybeInitializedLocals, MaybeLiveLocals};
use rustc_mir_dataflow::Analysis;

use rustc_middle::{mir::traversal::preorder, mir::Body, ty::TyCtxt};

pub fn debug<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    let mut init = MaybeInitializedLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut init2 = MaybeInitializedLocals
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
            init.seek_before_primary_effect(loc);
            init2.seek_after_primary_effect(loc);
            live.seek_before_primary_effect(loc);
            live2.seek_after_primary_effect(loc);

            println!(
                "{:<45} init={:?} -> {:?} live={:?} <- {:?}",
                format!("{:?}", statement),
                init.get(),
                init2.get(),
                live.get(),
                live2.get(),
            );
            loc = loc.successor_within_block();
        }

        println!(
            "{:<45} init={:?} -> {:?} live={:?} <- {:?}\n",
            format!("{:?}", bbd.terminator().kind),
            init.get(),
            init2.get(),
            live.get(),
            live2.get(),
        );
    }
}
