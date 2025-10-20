#![feature(rustc_private, register_tool)]
#![feature(box_patterns)]
#![feature(never_type, try_blocks)]
#![feature(closure_lifetime_binder, assert_matches)]
#![feature(if_let_guard, slice_as_array)]

extern crate either;
#[macro_use]
extern crate log;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_ir;
extern crate rustc_ast_pretty;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_fluent_macro;
extern crate rustc_hashes;
extern crate rustc_hir;
extern crate rustc_hir_typeck;
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
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

pub mod callbacks;

mod analysis;
mod backend;
mod cleanup_spec_closures;
mod contracts_items;
mod ctx;
mod extended_location;
mod gather_spec_closures;
mod lints;
mod metadata;
mod naming;
mod translated_item;
mod translation;
mod util;
mod validate;
mod very_stable_hash;

rustc_fluent_macro::fluent_messages! { "../messages.ftl" }
