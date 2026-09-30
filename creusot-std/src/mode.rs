//! Proof modes

use crate::prelude::*;

#[opaque]
#[builtin("creusot.prelude.Mode.t")]
#[intrinsic("mode_type")]
pub struct Mode(());

impl Mode {
    /// When `true`, panics are forbidden.
    ///
    /// The core panicking functions have precondition `!mode!().nopanic()`.
    ///
    /// Important: there remain panics that this does not rule out,
    /// notably including panics in memory allocation, notably for
    /// `Box`, `Vec` and other collections.
    #[logic]
    #[builtin("creusot.prelude.Mode.nopanic")]
    #[intrinsic("mode_nopanic")]
    pub fn nopanic(self) -> bool {
        dead
    }

    /// When `true`, all loops and recursive functions must terminate.
    ///
    /// Proof obligations related to variants are guarded with `mode!().terminates()`.
    #[logic]
    #[builtin("creusot.prelude.Mode.terminates")]
    #[intrinsic("mode_terminates")]
    pub fn terminates(self) -> bool {
        dead
    }

    /// Ghost mode, enabled by `ghost!{}` blocks.
    ///
    /// Implies [`Self::nopanic`] and [`Self::terminates`].
    #[logic]
    #[builtin("creusot.prelude.Mode.ghost_")]
    #[intrinsic("mode_ghost")]
    pub fn ghost(self) -> bool {
        dead
    }

    #[logic]
    #[builtin("creusot.prelude.Mode.into_ghost")]
    #[intrinsic("mode_into_ghost")]
    pub fn into_ghost(self) -> Self {
        dead
    }

    /// Basic mode
    ///
    /// This mode is used in the translation of `const` blocks, and as an arbitrary mode
    /// in some contracts of higher-order functions, notably iterators.
    ///
    /// - `nopanic()` is enabled.
    /// - `terminates()` is disabled: nonterminating `const` code will just
    ///   lead to code that doesn't compile.
    #[logic]
    #[builtin("creusot.prelude.Mode.program_mode")]
    pub fn program_mode() -> Mode {
        dead
    }
}
