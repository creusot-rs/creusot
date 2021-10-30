#![feature(rustc_private)]
#![feature(in_band_lifetimes)]
#![feature(min_specialization)]

extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;

pub mod decoder;
pub mod encoder;
