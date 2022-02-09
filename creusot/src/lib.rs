#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns, control_flow_enum, drain_filter)]
#![feature(in_band_lifetimes, let_else)]
#![register_tool(creusot)]

extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_macros;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_mir_dataflow;
extern crate rustc_mir_transform;
extern crate rustc_resolve;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_typeck;
extern crate smallvec;
#[macro_use]
extern crate log;

mod analysis;
pub mod arg_value;
pub mod callbacks;
mod cleanup_spec_closures;
pub mod clone_map;
pub(crate) mod creusot_items;
pub mod ctx;
#[allow(dead_code)]
mod debug;
mod extended_location;
mod gather_spec_closures;
pub mod options;
mod resolve;
// #[allow(dead_code)]
mod rustc_extensions;
mod translation;
pub mod util;
use translation::*;
mod error;
pub mod metadata;
mod translated_item;
mod validate;
