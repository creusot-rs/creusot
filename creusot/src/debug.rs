use rustc_mir_dataflow::{Analysis, impls::MaybeUninitializedPlaces, move_paths::MoveData};

use rustc_middle::{
    mir::{Body, traversal::preorder},
    ty::TyCtxt,
};

use crate::analysis::MaybeLiveExceptDrop;

pub fn debug<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    let move_data = MoveData::gather_moves(body, tcx, |_| true);

    let mut uninit = MaybeUninitializedPlaces::new(tcx, body, &move_data)
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);

    let mut uninit2 = MaybeUninitializedPlaces::new(tcx, body, &move_data)
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);

    let mut live = MaybeLiveExceptDrop::new(tcx, body, &move_data)
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);

    let mut live2 = MaybeLiveExceptDrop::new(tcx, body, &move_data)
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);

    for (bb, bbd) in preorder(body) {
        if bbd.is_cleanup {
            continue;
        }
        println!("{:?}", bb);
        let mut loc = bb.start_location();
        for statement in &bbd.statements {
            uninit.seek_before_primary_effect(loc);
            uninit2.seek_after_primary_effect(loc);
            live.seek_before_primary_effect(loc);
            live2.seek_after_primary_effect(loc);

            println!(
                "{:<45} uninit={:?} -> {:?} live={:?} <- {:?}",
                format!("{:?}", statement),
                uninit.get().iter().collect::<Vec<_>>(),
                uninit2.get().iter().collect::<Vec<_>>(),
                live.get().iter().collect::<Vec<_>>(),
                live2.get().iter().collect::<Vec<_>>(),
            );
            loc = loc.successor_within_block();
        }

        uninit.seek_before_primary_effect(loc);
        uninit2.seek_after_primary_effect(loc);
        live.seek_before_primary_effect(loc);
        live2.seek_after_primary_effect(loc);

        println!(
            "{:<45} uninit={:?} -> {:?} live={:?} <- {:?}",
            format!("{:?}", bbd.terminator().kind),
            uninit.get().iter().collect::<Vec<_>>(),
            uninit2.get().iter().collect::<Vec<_>>(),
            live.get().iter().collect::<Vec<_>>(),
            live2.get().iter().collect::<Vec<_>>(),
        );
    }
}
