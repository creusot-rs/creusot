use rustc_middle::mir::Location;
use rustc_mir_dataflow::{self as dataflow, Analysis, ResultsCursor};

// Dataflow locations
#[derive(Debug, Copy, Clone)]
pub enum ExtendedLocation {
    Start(Location), // Before the statement
    Mid(Location), // For assignments and calls: after the RHS is computed, but before the LHS is written to
    End(Location), // After the statement
}

// Rust hides the real `Direction` trait from me, this hack recreates it
pub trait Dir {
    fn is_forward() -> bool;
}

impl Dir for dataflow::Forward {
    fn is_forward() -> bool {
        true
    }
}

impl Dir for dataflow::Backward {
    fn is_forward() -> bool {
        false
    }
}

impl ExtendedLocation {
    pub(crate) fn seek_to<'tcx, A>(self, cursor: &mut ResultsCursor<'_, 'tcx, A>)
    where
        A: Analysis<'tcx, Direction: Dir>,
    {
        use ExtendedLocation::*;
        match self {
            Start(_) => (),
            Mid(loc) => assert!(cursor.body().stmt_at(loc).is_right()),
            End(loc) => assert!(cursor.body().stmt_at(loc).is_left()),
        }
        if A::Direction::is_forward() {
            match self {
                Start(loc) => cursor.seek_before_primary_effect(loc),
                Mid(loc) | End(loc) => cursor.seek_after_primary_effect(loc),
            }
        } else {
            match self {
                Start(loc) => cursor.seek_after_primary_effect(loc),
                Mid(loc) | End(loc) => cursor.seek_before_primary_effect(loc),
            }
        }
    }

    pub(crate) fn loc(self) -> Location {
        match self {
            ExtendedLocation::Start(loc)
            | ExtendedLocation::Mid(loc)
            | ExtendedLocation::End(loc) => loc,
        }
    }
}
