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
use rustc_data_structures::{
    fx::FxHashMap,
    stable_hasher::{Hash64, StableHasher},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{
    def_id::{StableCrateId, LOCAL_CRATE},
    source_map::StableSourceFileId,
    FileName, SourceFile,
};
use std::hash::Hash;

#[derive(Encodable, Decodable, Eq, PartialEq, Hash, Clone, Copy)]
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
    file_name_hash: Hash64,
    stable_crate_id: StableCrateId,
}

impl EncodedSourceFileId {
    fn translate(&self, tcx: TyCtxt<'_>) -> StableSourceFileId {
        let cnum = tcx.stable_crate_id_to_crate_num(self.stable_crate_id);
        StableSourceFileId { file_name_hash: self.file_name_hash, cnum }
    }

    fn new(tcx: TyCtxt<'_>, file: &SourceFile) -> EncodedSourceFileId {
        if file.cnum == LOCAL_CRATE {
            /* Cf rustc_metadata::rmeta::encode_source_map */
            if let FileName::Real(ref original_file_name) = file.name {
                let adapted_file_name =
                    tcx.sess.source_map().path_mapping().to_embeddable_absolute_path(
                        original_file_name.clone(),
                        &tcx.sess.opts.working_dir,
                    );
                if adapted_file_name != *original_file_name {
                    let file_name_hash = {
                        let mut hasher = StableHasher::new();
                        FileName::Real(adapted_file_name).hash(&mut hasher);
                        hasher.finish::<_>()
                    };
                    return EncodedSourceFileId {
                        file_name_hash,
                        stable_crate_id: tcx.stable_crate_id(LOCAL_CRATE),
                    };
                }
            }
        }
        let source_file_id = StableSourceFileId::new(file);
        EncodedSourceFileId {
            file_name_hash: source_file_id.file_name_hash,
            stable_crate_id: tcx.stable_crate_id(source_file_id.cnum),
        }
    }
}

#[derive(Decodable, Encodable)]
struct Footer {
    file_index_to_stable_id: FxHashMap<SourceFileIndex, EncodedSourceFileId>,
    syntax_contexts: FxHashMap<u32, AbsoluteBytePos>,
    expn_data: FxHashMap<(StableCrateId, u32), AbsoluteBytePos>,
}
