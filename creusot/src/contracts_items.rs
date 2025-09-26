//! This modules groups together special items defined in [`creusot_contracts`].
//!
//! This includes attributes like `#[creusot::logic]`, and intrinsics like `Snapshot`.

mod attributes;
mod intrinsics;

pub(crate) use attributes::*;
pub(crate) use intrinsics::*;
