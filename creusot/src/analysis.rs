use rustc_middle::mir::{visit::Visitor, BasicBlock, Body, Local, Location, Place, Rvalue};
use std::collections::HashMap;

pub struct DiscrTyMap<'tcx> {
    discr_map: HashMap<(BasicBlock, Local), Place<'tcx>>,
}

impl<'tcx> DiscrTyMap<'tcx> {
    pub fn analyze(body: &Body<'tcx>) -> HashMap<(BasicBlock, Local), Place<'tcx>> {
        let mut m = DiscrTyMap { discr_map: HashMap::new() };
        m.visit_body(body);
        m.discr_map
    }
}

impl<'tcx> Visitor<'tcx> for DiscrTyMap<'tcx> {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Discriminant(pl) = rvalue {
            self.discr_map.insert((location.block, place.local), pl.to_owned());
        }
    }
}
