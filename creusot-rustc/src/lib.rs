#![feature(rustc_private)]

pub extern crate rustc_ast as ast;
pub extern crate rustc_borrowck as borrowck;
pub extern crate rustc_data_structures as data_structures;
pub extern crate rustc_driver as driver;
pub extern crate rustc_errors as errors;
pub extern crate rustc_hir as hir;
pub extern crate rustc_index as index;
pub extern crate rustc_infer as infer;
pub extern crate rustc_interface as interface;
pub extern crate rustc_macros as macros;
pub extern crate rustc_metadata as metadata;
pub extern crate rustc_middle as middle;
pub extern crate rustc_mir_build as mir_build;
pub extern crate rustc_mir_dataflow as dataflow;
pub extern crate rustc_mir_transform as mir_transform;
pub extern crate rustc_mir_transform as transform;
pub extern crate rustc_resolve as resolve;
pub extern crate rustc_serialize as serialize;
pub extern crate rustc_session as session;
pub extern crate rustc_smir as smir;
pub extern crate rustc_span as span;
pub extern crate rustc_target as target;
pub extern crate rustc_trait_selection as trait_selection;
pub extern crate rustc_type_ir as type_ir;
pub extern crate rustc_typeck as typeck;
