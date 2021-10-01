#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns, control_flow_enum)]
#![feature(in_band_lifetimes)]
#![register_tool(creusot)]
#![feature(const_panic)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
// extern   crate rustc_mir;
extern crate rustc_mir_build;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate smallvec;

#[macro_use]
extern crate log;

mod analysis;
pub mod clone_map;
pub mod ctx;
mod extended_location;
mod gather_invariants;
mod resolve;
mod translation;
pub mod util;

#[allow(dead_code)]
mod debug;

#[allow(dead_code)]
mod rustc_extensions;

mod cleanup_spec_closures;

pub mod arg_value;
pub mod callbacks;
pub mod options;

use translation::*;
