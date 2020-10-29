// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// Code for loading an manipulating Polonius facts.
///
/// This code was adapted from the
/// [Polonius](https://github.com/rust-lang-nursery/polonius/blob/master/src/facts.rs)
/// source code.
use csv::ReaderBuilder;
use regex::Regex;
use rustc_index::vec::Idx;
use rustc_middle::mir::Local;
use serde::de::DeserializeOwned;
use std::hash::Hash;
use std::path::Path;
use std::str::FromStr;

use lazy_static::*;

use polonius_engine;

rustc_index::newtype_index! {
    pub struct MovePathIndex {
        DEBUG_FORMAT = "mp{}" //"
    }
}

impl polonius_engine::Atom for MovePathIndex {
    fn index(self) -> usize {
        Idx::index(self)
    }
}

rustc_index::newtype_index! {
    pub struct Loan {
        DEBUG_FORMAT = "L{}" //"
    }
}

impl polonius_engine::Atom for Loan {
    fn index(self) -> usize {
        Idx::index(self)
    }
}

rustc_index::newtype_index! {
    pub struct Region {
        DEBUG_FORMAT = "R{}" //"
    }
}

impl polonius_engine::Atom for Region {
    fn index(self) -> usize {
        Idx::index(self)
    }
}

impl FromStr for Region {
    type Err = ();

    fn from_str(region: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^\\'_#(?P<id>\d+)r$").unwrap();
        }
        let caps = RE.captures(region).unwrap();
        let id: usize = caps["id"].parse().unwrap();
        Ok(id.into())
    }
}

impl FromStr for MovePathIndex {
    type Err = ();

    fn from_str(region: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^mp(?P<id>\d+)$").unwrap();
        }
        let caps = RE.captures(region).unwrap();
        let id: usize = caps["id"].parse().unwrap();
        Ok(id.into())
    }
}

impl FromStr for Loan {
    type Err = ();

    fn from_str(loan: &str) -> Result<Self, Self::Err> {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^bw(?P<id>\d+)$").unwrap();
        }
        let caps = RE.captures(loan).unwrap();
        let id: usize = caps["id"].parse().unwrap();
        Ok(id.into())
    }
}

use super::location_table::*;

#[derive(Copy, Clone, Debug)]
pub struct CreusotFacts;

impl polonius_engine::FactTypes for CreusotFacts {
    type Loan = Loan;
    type Origin = Region;
    type Point = LocationIndex;
    type Variable = Local;
    type Path = MovePathIndex;
}

pub type AllInputFacts = polonius_engine::AllFacts<CreusotFacts>;
pub type AllOutputFacts = polonius_engine::Output<CreusotFacts>;

trait InternTo<FromType, ToType> {
    fn intern(&mut self, element: FromType) -> ToType;
}

impl InternTo<String, Region> for FactLoader {
    fn intern(&mut self, element: String) -> Region {
        element.parse().unwrap()
    }
}

impl InternTo<String, Loan> for FactLoader {
    fn intern(&mut self, element: String) -> Loan {
        element.parse().unwrap()
    }
}

impl InternTo<String, LocationIndex> for FactLoader {
    fn intern(&mut self, element: String) -> LocationIndex {
        match element.parse().unwrap() {
            RichLocation::Start(l) => self.interner.start_index(l),
            RichLocation::Mid(l) => self.interner.mid_index(l),
        }
    }
}

impl InternTo<String, MovePathIndex> for FactLoader {
    fn intern(&mut self, element: String) -> MovePathIndex {
        element.parse().unwrap()
    }
}

impl InternTo<String, Local> for FactLoader {
    fn intern(&mut self, element: String) -> Local {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"^_(?P<id>\d+)$").unwrap();
        }
        let caps = RE.captures(&element).unwrap();
        let id: usize = caps["id"].parse().unwrap();
        id.into()
    }
}

impl<A, B> InternTo<(String, String), (A, B)> for FactLoader
where
    FactLoader: InternTo<String, A>,
    FactLoader: InternTo<String, B>,
{
    fn intern(&mut self, (e1, e2): (String, String)) -> (A, B) {
        (self.intern(e1), self.intern(e2))
    }
}

impl<A, B, C> InternTo<(String, String, String), (A, B, C)> for FactLoader
where
    FactLoader: InternTo<String, A>,
    FactLoader: InternTo<String, B>,
    FactLoader: InternTo<String, C>,
{
    fn intern(&mut self, (e1, e2, e3): (String, String, String)) -> (A, B, C) {
        (self.intern(e1), self.intern(e2), self.intern(e3))
    }
}

fn load_facts_from_file<T: DeserializeOwned>(facts_dir: &Path, facts_type: &str) -> Vec<T> {
    let filename = format!("{}.facts", facts_type);
    let facts_file = facts_dir.join(&filename);
    let mut reader =
        ReaderBuilder::new().delimiter(b'\t').has_headers(false).from_path(facts_file).unwrap();
    reader.deserialize().map(|row| row.unwrap()).collect()
}

pub struct FactLoader {
    pub interner: LocationTable,
    pub facts: AllInputFacts,
}

impl FactLoader {
    pub fn new(loc_map: LocationTable) -> Self {
        Self { interner: loc_map, facts: AllInputFacts::default() }
    }
    pub fn load_all_facts(&mut self, facts_dir: &Path) {
        let facts = load_facts::<(_, _, _), _>(self, facts_dir, "borrow_region");
        self.facts.borrow_region.extend(facts);

        let facts = load_facts::<(_, _, _), _>(self, facts_dir, "borrow_region");
        self.facts.borrow_region.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "cfg_edge");
        self.facts.cfg_edge.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "child_path");
        self.facts.child_path.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "drop_of_var_derefs_origin");
        self.facts.drop_of_var_derefs_origin.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "invalidates");
        self.facts.invalidates.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "killed");
        self.facts.killed.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "known_subset");
        self.facts.known_subset.extend(facts);

        let facts = load_facts::<(_, _, _), _>(self, facts_dir, "outlives");
        self.facts.outlives.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "path_accessed_at_base");
        self.facts.path_accessed_at_base.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "path_is_var");
        self.facts.path_is_var.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "path_moved_at_base");
        self.facts.path_moved_at_base.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "placeholder");
        self.facts.placeholder.extend(facts);

        let facts = load_facts::<_, Region>(self, facts_dir, "universal_region");
        self.facts.universal_region.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "use_of_var_derefs_origin");
        self.facts.use_of_var_derefs_origin.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "var_defined_at");
        self.facts.var_defined_at.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "var_dropped_at");
        self.facts.var_dropped_at.extend(facts);

        let facts = load_facts::<(_, _), _>(self, facts_dir, "var_used_at");
        self.facts.var_used_at.extend(facts);
    }
}

fn load_facts<F: DeserializeOwned, T>(
    interner: &mut FactLoader,
    facts_dir: &Path,
    facts_type: &str,
) -> Vec<T>
where
    FactLoader: InternTo<F, T>,
{
    load_facts_from_file(facts_dir, facts_type)
        .into_iter()
        .map(|fact| interner.intern(fact))
        .collect()
}
