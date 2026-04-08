//! Proof modes

use crate::prelude::*;

#[opaque]
#[builtin("creusot.prelude.Mode.t")]
#[intrinsic("mode_type")]
pub struct Mode(());

impl Mode {
    #[logic]
    #[builtin("creusot.prelude.Mode.nopanic")]
    #[intrinsic("mode_nopanic")]
    pub fn nopanic(self) -> bool {
        dead
    }

    #[logic]
    #[builtin("creusot.prelude.Mode.terminates")]
    #[intrinsic("mode_terminates")]
    pub fn terminates(self) -> bool {
        dead
    }

    #[logic]
    #[builtin("creusot.prelude.Mode.ghost_")]
    #[intrinsic("mode_ghost")]
    pub fn ghost(self) -> bool {
        dead
    }

    #[logic]
    #[builtin("creusot.prelude.Mode.into_ghost")]
    pub fn into_ghost(self) -> Self {
        dead
    }
}

#[logic]
#[builtin("creusot.prelude.Mode.program_mode")]
pub fn program_mode() -> Mode {
    dead
}
