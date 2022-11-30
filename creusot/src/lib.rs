#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns, control_flow_enum, drain_filter)]
#![feature(let_chains, never_type, try_blocks, slice_take)]

#[macro_use]
extern crate log;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_smir;
extern crate rustc_type_ir;

mod analysis;
pub(crate) mod backend;
pub mod callbacks;
mod cleanup_spec_closures;
#[allow(dead_code)]
pub(crate) mod clone_map;
#[allow(dead_code)]
pub(crate) mod creusot_items;
#[allow(dead_code)]
pub(crate) mod ctx;

mod extended_location;
mod gather_spec_closures;
pub mod options;
mod resolve;
// #[allow(dead_code)]
mod rustc_extensions;
#[allow(dead_code)]
mod translation;
pub(crate) mod util;
use translation::*;
mod error;
pub(crate) mod metadata;
#[allow(dead_code)]
mod translated_item;
mod validate;
