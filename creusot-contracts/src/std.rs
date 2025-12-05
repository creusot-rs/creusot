//! Specifications for the `std` crate
mod array;
mod borrow;
pub mod cell;
pub mod clone;
pub mod char;
pub mod cmp;
pub mod convert;
pub mod default;
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
pub mod result;
pub mod slice;
pub mod string;
pub mod time;
mod tuples;


// Every std-dependent part of the Creusot Standard Library must be disabled when 
// compiling with [no_std].
#[cfg(feature = "std")]
pub mod boxed;

#[cfg(feature = "std")]
pub mod collections {
    pub mod hash_map;
    pub mod hash_set;
}

#[cfg(feature = "std")]
pub mod deque;

#[cfg(feature = "std")]
pub mod rc;

#[cfg(feature = "std")]
mod sync;

#[cfg(feature = "std")]
pub mod vec;
