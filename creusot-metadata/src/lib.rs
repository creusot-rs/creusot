#![feature(rustc_private)]
#![feature(min_specialization)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
#[macro_use]
extern crate rustc_macros;

// Tags used for encoding Spans:
const TAG_FULL_SPAN: u8 = 0;
const TAG_PARTIAL_SPAN: u8 = 1;

// Tags for encoding Symbol's
const SYMBOL_STR: u8 = 0;
const SYMBOL_OFFSET: u8 = 1;
const SYMBOL_PREINTERNED: u8 = 2;

mod decoder;
mod encoder;

pub use decoder::decode_metadata;
pub use encoder::encode_metadata;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_span::{SourceFile, StableSourceFileId, def_id::StableCrateId};
use std::hash::Hash;

#[derive(Encodable, Decodable, Eq, PartialEq, Hash, Clone, Copy, Debug)]
struct SourceFileIndex(u32);

#[derive(Encodable, Decodable, Clone, Copy)]
pub struct AbsoluteBytePos(u64);

impl AbsoluteBytePos {
    fn new(pos: usize) -> AbsoluteBytePos {
        AbsoluteBytePos(pos.try_into().unwrap())
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// An `EncodedSourceFileId` is the same as a `StableSourceFileId` except that
/// the source crate is represented as a [StableCrateId] instead of as a
/// `CrateNum`. This way `EncodedSourceFileId` can be encoded and decoded
/// without any additional context, i.e. with a simple `opaque::Decoder` (which
/// is the only thing available when decoding the [Footer].
#[derive(Encodable, Decodable, Clone, Debug)]
struct EncodedSourceFileId {
    stable_source_file_id: StableSourceFileId,
    stable_crate_id: StableCrateId,
}

impl EncodedSourceFileId {
    #[inline]
    fn new(tcx: TyCtxt<'_>, file: &SourceFile) -> EncodedSourceFileId {
        EncodedSourceFileId {
            stable_source_file_id: file.stable_id,
            stable_crate_id: tcx.stable_crate_id(file.cnum),
        }
    }
}

#[derive(Decodable, Encodable)]
struct Footer {
    file_index_to_stable_id: FxHashMap<SourceFileIndex, EncodedSourceFileId>,
    syntax_contexts: FxHashMap<u32, AbsoluteBytePos>,
    expn_data: FxHashMap<(StableCrateId, u32), AbsoluteBytePos>,
}
