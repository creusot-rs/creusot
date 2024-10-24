//! This modules groups together special items defined in [`creusot_contracts`].
//!
//! This includes attributes like `#[creusot::logic]`, and diagnostic items like `Snapshot`.

mod attributes;
mod diagnostic_items;

pub(crate) use attributes::*;
pub(crate) use diagnostic_items::*;
