use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    path::PathBuf,
};

use rustc_hir::definitions::DefPath;

use rustc_middle::mir::{BasicBlock, Body, Local, Location};

// use smallvec::SmallVec;
// use smallvec::SmallVec;

pub mod facts;
pub mod location_table;

pub struct PoloniusInfo<'a, 'tcx> {
    pub facts: facts::AllOutputFacts,
    pub in_facts: facts::AllInputFacts,
    loan_vars: HashMap<facts::Loan, Location>,
    loc_table: location_table::LocationTable,
    body: &'a Body<'tcx>,
}

impl<'a, 'tcx> PoloniusInfo<'a, 'tcx> {
    pub fn new(body: &'a Body<'tcx>, def_path: DefPath) -> Self {
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

        let loan_vars = facts_loader
            .facts
            .borrow_region
            .iter()
            .map(|(_, l, v)| (*l, loc_table.to_location(*v).to_loc()))
            .collect();

        PoloniusInfo { facts: output, in_facts: facts_loader.facts, loan_vars, loc_table, body }
    }

    fn predecessors(&self, mut loc: Location) -> Vec<Location> {
        if loc.statement_index == 0 {
            self.body.predecessors()[loc.block]
                .iter()
                .map(|bb| self.body.terminator_loc(*bb))
                .collect()
        } else {
            loc.statement_index -= 1;
            vec![loc]
        }
    }

    pub fn loans_live_here(&self, loc: Location) -> Vec<facts::Loan> {
        (&self.facts.borrow_live_at[&self.loc_table.mid_index(loc)]).to_owned()
    }

    pub fn loan_created_at(&self, loan: facts::Loan) -> Location {
        self.loan_vars[&loan]
    }

    pub fn loans_dying_at_start(&self, loc: Location) -> Vec<facts::Loan> {
        let predecessors = self.predecessors(loc);

        // Set of all loans that were alive in predecessor locations
        let pred_loans: HashSet<_> = predecessors
            .iter()
            .flat_map(|pred| &self.facts.borrow_live_at[&self.loc_table.mid_index(*pred)])
            .collect();

        // Loans live at start of location
        let live_at_start: HashSet<_> =
            self.facts.borrow_live_at[&self.loc_table.start_index(loc)].iter().collect();

        (&pred_loans - &live_at_start).into_iter().cloned().collect()
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
