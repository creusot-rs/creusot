//! Specifications for the `std` crate
mod array;
mod borrow;
mod boxed;
pub mod cell;
pub mod clone;
pub mod collections {
    pub mod hash_map;
    pub mod hash_set;
}
pub mod char;
pub mod cmp;
pub mod convert;
pub mod default;
pub mod deque;
pub mod fmt;
pub mod hint;
pub mod intrinsics;
pub mod io;
pub mod iter;
pub mod mem;
pub mod num;
pub mod ops;
pub mod option;
pub mod panicking;
pub mod ptr;
pub mod range;
pub mod rc;
pub mod result;
pub mod slice;
pub mod string;
mod sync;
pub mod time;
mod tuples;
pub mod vec;
