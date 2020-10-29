use std::{collections::{BTreeMap, BTreeSet, HashMap}, path::PathBuf};

use rustc_hir::definitions::DefPath;
use rustc_middle::mir::{BasicBlock, Body, Local, Location};

pub mod facts;
pub mod location_table;

pub struct PoloniusInfo {
    pub facts: facts::AllOutputFacts,
    pub in_facts: facts::AllInputFacts,
    loan_vars: HashMap<facts::Loan, Location>,
    loc_table: location_table::LocationTable,
    block_successors: SuccessorMap,
}

type SuccessorMap = HashMap<Location, Vec<Location>>;

fn successor_map(body: &Body) -> SuccessorMap {
    let mut map = HashMap::new();

    for (bb, bbd) in body.basic_blocks().iter_enumerated() {
        map.insert(
            body.terminator_loc(bb),
            bbd.terminator
                .as_ref()
                .unwrap()
                .successors()
                .cloned()
                .map(|bb| bb.start_location())
                .collect(),
        );
    }

    return map;
}

impl PoloniusInfo {
    pub fn new(body: &Body, def_path: DefPath) -> Self {
        let loc_table = location_table::LocationTable::new(&body);
        let dir_path = PathBuf::from("nll-facts").join(def_path.to_filename_friendly_no_crate());
        log::debug!("Reading facts from: {:?}", dir_path);

        let mut facts_loader = facts::FactLoader::new(loc_table);
        facts_loader.load_all_facts(&dir_path);

        let output = polonius_engine::Output::compute(
            &facts_loader.facts,
            polonius_engine::Algorithm::Naive,
            true,
        );

        let loc_table = facts_loader.interner;

        let loan_vars = facts_loader.facts.borrow_region.iter().map(|(_, l, v)| {
            (*l, loc_table.to_location(*v).to_loc())
        }).collect();

        PoloniusInfo {
            facts: output,
            in_facts: facts_loader.facts,
            loan_vars,
            loc_table,
            block_successors: successor_map(body),
        }
    }

    fn successors(&self, loc: Location) -> Vec<Location> {
        self.block_successors
            .get(&loc)
            .map(|v| v.to_owned())
            .unwrap_or_else(|| vec![loc.successor_within_block()])
    }

    pub fn loans_live_here(&self, loc: Location) -> Vec<facts::Loan> {
        (&self.facts.borrow_live_at[&self.loc_table.mid_index(loc)]).to_owned()
    }

    pub fn loan_created_at(&self, loan: facts::Loan) -> Location {
        self.loan_vars[&loan]
    }

    pub fn loans_dying_here(&self, loc: Location) -> Vec<facts::Loan> {
        let live_borrows : &Vec<_> = &self.facts.borrow_live_at[&self.loc_table.mid_index(loc)];
        let successors = self.successors(loc);

        live_borrows.into_iter().filter(|loan| {
            // TODO what happens if the loan dies in _one_ successor?
            !successors.iter().any(|s| {
                let succ_loc = self.loc_table.start_index(*s);
                self.facts.borrow_live_at[&succ_loc].contains(&loan)
            })
        }).cloned().collect()

    }

    pub fn origins_live_at_entry(&self, loc: Location) -> &Vec<facts::Region> {
        let entry_point = self.loc_table.start_index(loc);

        &self.facts.origin_live_on_entry[&entry_point]
    }

    pub fn restricts(&self, loc: Location) -> &BTreeMap<facts::Region, BTreeSet<facts::Loan>> {
        let point = self.loc_table.mid_index(loc);
        &self.facts.restricts[&point]
    }
    // pub fn loans_dying_here(&self, loc: Location) -> Vec<facts::Loan> {
    //     let start_borrows : &Vec<_> = &self.facts.borrow_live_at[&self.loc_table.start_index(loc)];
    //     let mid_borrows : &Vec<_> = &self.facts.borrow_live_at[&self.loc_table.mid_index(loc)];

    //     dbg!(loc, start_borrows, mid_borrows);
    //     start_borrows.iter().filter(|loan| {
    //         !mid_borrows.contains(loan)
    //     }).cloned().collect()
    // }
}
