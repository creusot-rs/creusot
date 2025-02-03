#![feature(rustc_private, register_tool)]
#![feature(box_patterns, extract_if)]
#![feature(let_chains, never_type, try_blocks)]
#![feature(closure_lifetime_binder)]
#![feature(if_let_guard, slice_take)]

extern crate either;
#[macro_use]
extern crate log;
extern crate rustc_ast;
extern crate rustc_ast_ir;
extern crate rustc_ast_pretty;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_fluent_macro;
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
extern crate rustc_next_trait_solver;
extern crate rustc_resolve;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

pub mod callbacks;
pub mod options;

mod analysis;
mod backend;
mod cleanup_spec_closures;
mod contracts_items;
mod creusot_items;
mod ctx;
#[allow(dead_code)]
mod debug;
mod error;
mod extended_location;
mod gather_spec_closures;
mod lints;
mod metadata;
mod naming;
mod resolve;
mod run_why3;
mod translated_item;
mod translation;
use translation::*;
mod util;
mod validate;
mod validate_terminates;
mod very_stable_hash;

rustc_fluent_macro::fluent_messages! { "../messages.ftl" }
