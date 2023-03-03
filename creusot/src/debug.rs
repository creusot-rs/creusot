use rustc_mir_dataflow::Analysis;

use rustc_middle::{
    mir::{traversal::preorder, Body},
    ty::TyCtxt,
};

use crate::analysis::{MaybeInitializedLocals, MaybeLiveExceptDrop, MaybeUninitializedLocals};

pub fn debug<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    let mut init = MaybeInitializedLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut init2 = MaybeInitializedLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut uninit = MaybeUninitializedLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut uninit2 = MaybeUninitializedLocals
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut live =
        MaybeLiveExceptDrop.into_engine(tcx, body).iterate_to_fixpoint().into_results_cursor(body);
    let mut live2 =
        MaybeLiveExceptDrop.into_engine(tcx, body).iterate_to_fixpoint().into_results_cursor(body);

    for (bb, bbd) in preorder(body) {
        if bbd.is_cleanup {
            continue;
        }
        println!("{:?}", bb);
        let mut loc = bb.start_location();
        for statement in &bbd.statements {
            init.seek_before_primary_effect(loc);
            init2.seek_after_primary_effect(loc);
            uninit.seek_before_primary_effect(loc);
            uninit2.seek_after_primary_effect(loc);
            live.seek_before_primary_effect(loc);
            live2.seek_after_primary_effect(loc);

            println!(
                "{:<45} uninit={:?} -> {:?} init={:?} -> {:?} live={:?} <- {:?}",
                format!("{:?}", statement),
                uninit.get().iter().collect::<Vec<_>>(),
                uninit2.get().iter().collect::<Vec<_>>(),
                init.get(),
                init2.get(),
                live.get().iter().collect::<Vec<_>>(),
                live2.get().iter().collect::<Vec<_>>(),
            );
            loc = loc.successor_within_block();
        }

        init.seek_before_primary_effect(loc);
        init2.seek_after_primary_effect(loc);
        uninit.seek_before_primary_effect(loc);
        uninit2.seek_after_primary_effect(loc);
        live.seek_before_primary_effect(loc);
        live2.seek_after_primary_effect(loc);

        println!(
            "{:<45} uninit={:?} -> {:?} init={:?} -> {:?} live={:?} <- {:?}",
            format!("{:?}", bbd.terminator().kind),
            uninit.get().iter().collect::<Vec<_>>(),
            uninit2.get().iter().collect::<Vec<_>>(),
            init.get(),
            init2.get(),
            live.get().iter().collect::<Vec<_>>(),
            live2.get().iter().collect::<Vec<_>>(),
        );
    }
}
