#![feature(rustc_private, register_tool)]
#![feature(box_patterns, control_flow_enum, extract_if)]
#![feature(let_chains, never_type, try_blocks)]

#[macro_use]
extern crate log;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_lint;
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
extern crate rustc_type_ir;

mod analysis;
pub(crate) mod backend;
pub mod callbacks;
mod cleanup_spec_closures;
pub(crate) mod creusot_items;
pub(crate) mod ctx;

#[allow(dead_code)]
pub(crate) mod debug;

mod extended_location;
mod gather_spec_closures;
pub mod options;
mod resolve;
mod translation;
pub(crate) mod util;
use translation::*;
mod error;
pub(crate) mod lints;
pub(crate) mod metadata;
mod run_why3;
mod translated_item;
mod validate;
