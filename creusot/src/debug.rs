use rustc_mir_dataflow::{
    impls::DefinitelyInitializedPlaces, move_paths::MoveData, Analysis, MoveDataParamEnv,
};

use rustc_middle::{
    mir::{traversal::preorder, Body},
    ty::TyCtxt,
};

use crate::analysis::MaybeLiveExceptDrop;

pub fn debug<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    let param_env = tcx.param_env(body.source.def_id());
    let move_data = MoveData::gather_moves(body, tcx, param_env, |_| true);
    let mdpe = MoveDataParamEnv { move_data, param_env };

    let mut init = DefinitelyInitializedPlaces::new(body, &mdpe)
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut init2 = DefinitelyInitializedPlaces::new(body, &mdpe)
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut live = MaybeLiveExceptDrop::new(body, &mdpe, tcx)
        .into_engine(tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

    let mut live2 = MaybeLiveExceptDrop::new(body, &mdpe, tcx)
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
            init.seek_before_primary_effect(loc);
            init2.seek_after_primary_effect(loc);
            live.seek_before_primary_effect(loc);
            live2.seek_after_primary_effect(loc);

            println!(
                "{:<45} init={:?} -> {:?} live={:?} <- {:?}",
                format!("{:?}", statement),
                init.get().0.iter().collect::<Vec<_>>(),
                init2.get().0.iter().collect::<Vec<_>>(),
                live.get().iter().collect::<Vec<_>>(),
                live2.get().iter().collect::<Vec<_>>(),
            );
            loc = loc.successor_within_block();
        }

        init.seek_before_primary_effect(loc);
        init2.seek_after_primary_effect(loc);
        live.seek_before_primary_effect(loc);
        live2.seek_after_primary_effect(loc);

        println!(
            "{:<45} init={:?} -> {:?} live={:?} <- {:?}",
            format!("{:?}", bbd.terminator().kind),
            init.get().0.iter().collect::<Vec<_>>(),
            init2.get().0.iter().collect::<Vec<_>>(),
            live.get().iter().collect::<Vec<_>>(),
            live2.get().iter().collect::<Vec<_>>(),
        );
    }
}
