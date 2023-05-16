use crate::{
    AbsoluteBytePos, EncodedSourceFileId, Footer, SourceFileIndex, SYMBOL_OFFSET,
    SYMBOL_PREINTERNED, SYMBOL_STR, TAG_FULL_SPAN, TAG_PARTIAL_SPAN,
};
use rustc_data_structures::{fx::FxHashMap, sync::Lrc};
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash, StableCrateId};
use rustc_middle::{
    implement_ty_decoder,
    ty::{codec::TyDecoder, Ty, TyCtxt},
};
use rustc_serialize::{
    opaque::{IntEncodedWithFixedSize, MemDecoder},
    Decodable, Decoder,
};
use rustc_span::{
    hygiene::{HygieneDecodeContext, SyntaxContextData},
    BytePos, ExpnData, ExpnHash, ExpnId, SourceFile, Span, Symbol, SyntaxContext, DUMMY_SP,
};

// This is only safe to decode the metadata of a single crate or the `ty_rcache` might confuse shorthands (see #360)
pub struct MetadataDecoder<'a, 'tcx> {
    opaque: MemDecoder<'a>,
    tcx: TyCtxt<'tcx>,
    ty_rcache: FxHashMap<usize, Ty<'tcx>>,
    file_index_to_file: FxHashMap<SourceFileIndex, Lrc<SourceFile>>,
    file_index_to_stable_id: FxHashMap<SourceFileIndex, EncodedSourceFileId>,
    syntax_contexts: &'a FxHashMap<u32, AbsoluteBytePos>,
    expn_data: FxHashMap<(StableCrateId, u32), AbsoluteBytePos>,
    hygiene_context: &'a HygieneDecodeContext,
}

impl<'a, 'tcx> MetadataDecoder<'a, 'tcx> {
    fn file_index_to_file(&mut self, index: SourceFileIndex) -> Lrc<SourceFile> {
        self.file_index_to_file
            .entry(index)
            .or_insert_with(|| {
                let stable_id = self.file_index_to_stable_id[&index].translate(self.tcx);
                self.tcx.cstore_untracked().import_source_files(self.tcx.sess, stable_id.cnum);
                self.tcx.sess.source_map().source_file_by_stable_id(stable_id).unwrap()
            })
            .clone()
    }
}

// Both the `CrateNum` and the `DefIndex` of a `DefId` can change in between two
// compilation sessions. We use the `DefPathHash`, which is stable across
// sessions, to map the old `DefId` to the new one.
impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for DefId {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> Self {
        let def_path_hash = DefPathHash::decode(d);
        d.tcx.def_path_hash_to_def_id(def_path_hash, &mut || panic!("Cannot resolve crate."))
    }
}

impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for CrateNum {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> CrateNum {
        let stable_id = StableCrateId::decode(d);
        d.tcx.stable_crate_id_to_crate_num(stable_id)
    }
}

// This impl makes sure that we get a runtime error when we try decode a
// `DefIndex` that is not contained in a `DefId`. Such a case would be problematic
// because we would not know how to transform the `DefIndex` to the current
// context.
impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for DefIndex {
    fn decode(_: &mut MetadataDecoder<'a, 'tcx>) -> DefIndex {
        panic!("trying to decode `DefIndex` outside the context of a `DefId`")
    }
}

impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for SyntaxContext {
    fn decode(decoder: &mut MetadataDecoder<'a, 'tcx>) -> Self {
        let syntax_contexts = decoder.syntax_contexts;
        rustc_span::hygiene::decode_syntax_context(decoder, &decoder.hygiene_context, |this, id| {
            // This closure is invoked if we haven't already decoded the data for the `SyntaxContext` we are deserializing.
            // We look up the position of the associated `SyntaxData` and decode it.
            let pos = syntax_contexts.get(&id).unwrap();
            this.with_position(pos.to_usize(), |decoder| SyntaxContextData::decode(decoder))
        })
    }
}

impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for ExpnId {
    fn decode(decoder: &mut MetadataDecoder<'a, 'tcx>) -> Self {
        let stable_id = StableCrateId::decode(decoder);
        let cnum = decoder.tcx.stable_crate_id_to_crate_num(stable_id);
        let index = u32::decode(decoder);

        let expn_id = rustc_span::hygiene::decode_expn_id(cnum, index, |_| {
            let pos = decoder.expn_data.get(&(stable_id, index)).unwrap();
            decoder.with_position(pos.to_usize(), |decoder| {
                let data = ExpnData::decode(decoder);
                let hash = ExpnHash::decode(decoder);
                (data, hash)
            })
        });
        expn_id
    }
}

impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for Span {
    fn decode(decoder: &mut MetadataDecoder<'a, 'tcx>) -> Self {
        let ctxt = SyntaxContext::decode(decoder);
        let tag: u8 = Decodable::decode(decoder);

        if tag == TAG_PARTIAL_SPAN {
            return DUMMY_SP.with_ctxt(ctxt);
        }

        debug_assert!(tag == TAG_FULL_SPAN);

        let source_file_index = SourceFileIndex::decode(decoder);
        let lo = BytePos::decode(decoder);
        let len = BytePos::decode(decoder);

        let file = decoder.file_index_to_file(source_file_index);
        let lo = file.start_pos + lo;
        let hi = lo + len;

        Span::new(lo, hi, ctxt, None)
    }
}

// copy&paste impl from rustc_metadata
impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for Symbol {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> Self {
        let tag = d.read_u8();

        match tag {
            SYMBOL_STR => {
                let s = d.read_str();
                Symbol::intern(s)
            }
            SYMBOL_OFFSET => {
                // read str offset
                let pos = d.read_usize();
                let old_pos = d.opaque.position();

                // move to str ofset and read
                d.opaque.set_position(pos);
                let s = d.read_str();
                let sym = Symbol::intern(s);

                // restore position
                d.opaque.set_position(old_pos);

                sym
            }
            SYMBOL_PREINTERNED => {
                let symbol_index = d.read_u32();
                Symbol::new_from_decoded(symbol_index)
            }
            _ => unreachable!(),
        }
    }
}

implement_ty_decoder!(MetadataDecoder<'a, 'tcx>);

impl<'a, 'tcx> TyDecoder for MetadataDecoder<'a, 'tcx> {
    // Whether crate-local information can be cleared while encoding
    const CLEAR_CROSS_CRATE: bool = true;

    type I = TyCtxt<'tcx>;

    fn interner(&self) -> Self::I {
        self.tcx
    }

    #[inline]
    fn peek_byte(&self) -> u8 {
        self.opaque.data[self.opaque.position()]
    }

    #[inline]
    fn position(&self) -> usize {
        self.opaque.position()
    }

    fn cached_ty_for_shorthand<F>(&mut self, shorthand: usize, or_insert_with: F) -> Ty<'tcx>
    where
        F: FnOnce(&mut Self) -> Ty<'tcx>,
    {
        if let Some(&ty) = self.ty_rcache.get(&shorthand) {
            return ty;
        }

        let ty = or_insert_with(self);
        self.ty_rcache.insert(shorthand, ty);
        ty
    }

    fn with_position<F, R>(&mut self, pos: usize, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let new_decoder = MemDecoder::new(self.opaque.data, pos);
        let old_decoder = std::mem::replace(&mut self.opaque, new_decoder);
        let r = f(self);
        self.opaque = old_decoder;
        r
    }

    fn decode_alloc_id(&mut self) -> rustc_middle::mir::interpret::AllocId {
        unimplemented!("decode_alloc_id")
    }
}

pub fn decode_metadata<'tcx, T: for<'a> Decodable<MetadataDecoder<'a, 'tcx>>>(
    tcx: TyCtxt<'tcx>,
    blob: &[u8],
) -> T {
    let footer = {
        let mut decoder = MemDecoder::new(blob, 0);
        decoder.set_position(blob.len() - IntEncodedWithFixedSize::ENCODED_SIZE);
        let footer_pos = IntEncodedWithFixedSize::decode(&mut decoder).0 as usize;
        decoder.set_position(footer_pos);
        Footer::decode(&mut decoder)
    };

    let mut decoder = MetadataDecoder {
        opaque: MemDecoder::new(blob, 0),
        tcx,
        ty_rcache: Default::default(),
        file_index_to_stable_id: footer.file_index_to_stable_id,
        file_index_to_file: Default::default(),
        syntax_contexts: &footer.syntax_contexts,
        expn_data: footer.expn_data,
        hygiene_context: &Default::default(),
    };
    T::decode(&mut decoder)
}
