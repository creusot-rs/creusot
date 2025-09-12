//! Interior mutability

mod pcell;
mod predcell;

pub use pcell::{PCell, PCellOwn};
pub use predcell::PredCell;
