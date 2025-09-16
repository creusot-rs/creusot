//! Interior mutability

mod permcell;
mod predcell;

pub use permcell::{PermCell, PermCellOwn};
pub use predcell::PredCell;
