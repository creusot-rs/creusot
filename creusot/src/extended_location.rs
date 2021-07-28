use rustc_middle::mir::Location;
use rustc_mir::dataflow::Analysis;
use rustc_mir::dataflow::{Results, ResultsCursor};
use std::borrow::Borrow;

// Dataflow locations
#[derive(Debug, Copy, Clone)]
pub enum ExtendedLocation {
    Start(Location),
    Mid(Location),
}

// Rust hides the real `Direction` trait from me, this hack recreates it
pub trait Dir {
    fn is_forward() -> bool;
}

impl Dir for rustc_mir::dataflow::Forward {
    fn is_forward() -> bool {
        true
    }
}

impl Dir for rustc_mir::dataflow::Backward {
    fn is_forward() -> bool {
        false
    }
}

impl ExtendedLocation {
    pub fn is_entry_loc(self) -> bool {
        if let Self::Start(loc) = self {
            loc == Location::START
        } else {
            false
        }
    }

    pub fn loc(&self) -> &Location {
        match self {
            Self::Start(l) => l,
            Self::Mid(l) => l,
        }
    }

    pub fn same_block(&self, other: Self) -> bool {
        self.loc().block == other.loc().block
    }

    pub fn seek_to<'tcx, A, R, D>(self, cursor: &mut ResultsCursor<'_, 'tcx, A, R>)
    where
        A: Analysis<'tcx, Direction = D>,
        D: Dir,
        R: Borrow<Results<'tcx, A>>,
    {
        use ExtendedLocation::*;
        if D::is_forward() {
            match self {
                Start(loc) => cursor.seek_before_primary_effect(loc),
                Mid(loc) => cursor.seek_after_primary_effect(loc),
            }
        } else {
            match self {
                Start(loc) => cursor.seek_after_primary_effect(loc),
                Mid(loc) => cursor.seek_before_primary_effect(loc),
            }
        }
    }
}
