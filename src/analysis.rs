use rustc_middle::mir::{BasicBlock, Body, Local, Location, Operand, Place, Rvalue, traversal::preorder, visit::Visitor};
use std::{collections::{BTreeMap, HashMap}};
// a mostly incorrect move analysis
// the result of this should explain how locals flowed into each other.

// An interval map with intervals restricted to be intra-basic block.
pub struct LocationIntervalMap<V> {
    vals: HashMap<BasicBlock, BTreeMap<usize, V>>,
}

impl<V> LocationIntervalMap<V> {
    // Insert a value for the interval starting at loc until the end of its basic block
    pub fn insert(&mut self, loc: Location, val: V) {
        let intervals = self.vals.entry(loc.block).or_default();
        intervals.insert(loc.statement_index, val);
    }

    // Get the nearest preceding value in loc's block.
    pub fn get(&mut self, loc: Location) -> Option<&V> {
        self.vals.get(&loc.block)?.range(..loc.statement_index + 1).last().map(|(_, v)| v)
    }
}

pub struct VarMoves {
    move_map: LocationIntervalMap<MoveMap>,
}

use rustc_middle::mir;

#[derive(Clone, Debug)]
pub struct MoveMap(HashMap<Local, Local>);

impl MoveMap {
  fn new () -> Self { MoveMap(HashMap::new())}

  pub fn get(&self, index: Local) -> Local {
      let mut res = index;

      while let Some(next) = self.0.get(&res) {
        res = *next
      }

      res
  }
}


impl VarMoves {
    pub fn new() -> Self {
        VarMoves { move_map: LocationIntervalMap { vals: HashMap::new() } }
    }

    pub fn compute(mut self, body: &Body<'_>) -> LocationIntervalMap<MoveMap> {
        for (bb, bbd) in preorder(&body) {
            self.visit_basic_block_data(bb, bbd);
        }
        self.move_map
    }
}

impl<'tcx> Visitor<'tcx> for VarMoves {
    fn visit_assign(
        &mut self,
        place: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        location: Location,
    ) {
        match rvalue {
            mir::Rvalue::Use(Operand::Move(rplace)) => {
                if let Some(rl) = rplace.as_local() {
                    if let Some(previous) = self.move_map.get(location) {
                        let mut new = previous.to_owned();
                        new.0.insert(rl, place.local);
                        self.move_map.insert(location, new);
                    } else {
                      let mut mm = MoveMap::new();
                      mm.0.insert(rl, place.local);

                        self.move_map
                            .insert(location, mm)
                    }
                }
            }
            _ => {}
        }
        self.super_assign(place, rvalue, location);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            mir::TerminatorKind::Call { args, .. } => {
                if self.move_map.get(location).is_none() {
                    return;
                }
                let mut new = self.move_map.get(location).unwrap().to_owned();
                for arg in args {
                    if let Operand::Move(pl) = arg {
                        new.0.remove(&pl.local);
                    }
                }

                self.move_map.insert(location, new);
            }
            _ => {}
        }

        if let Some(cur_map) = self.move_map.get(location) {
            let new = cur_map.to_owned();
            for s in terminator.successors() {
                let mut existing =
                    self.move_map.get(s.start_location()).map(|h| h.to_owned()).unwrap_or_else(|| MoveMap::new());
                existing.0.extend(&new.0);
                self.move_map.insert(s.start_location(), existing);
            }
        }

        self.super_terminator(terminator, location);
    }
}

pub struct DiscrTyMap<'tcx> { discr_map: HashMap<(BasicBlock, Local), Place<'tcx>>}

impl<'tcx> DiscrTyMap<'tcx> {
    pub fn analyze(body: &Body<'tcx>) -> HashMap<(BasicBlock, Local), Place<'tcx>> {
        let mut m = DiscrTyMap { discr_map: HashMap::new() };
        m.visit_body(body);
        m.discr_map
    }
}

impl<'tcx> Visitor<'tcx> for DiscrTyMap<'tcx> {
    fn visit_assign(&mut self, place: &Place< 'tcx>, rvalue: &Rvalue< 'tcx>, location: Location) {
        match rvalue {
            Rvalue::Discriminant(pl) => { self.discr_map.insert((location.block, place.local), pl.to_owned()); }
            _ => {}
        }
    }
}
