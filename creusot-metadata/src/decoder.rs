use crate::{
    AbsoluteBytePos, EncodedSourceFileId, Footer, SYMBOL_OFFSET, SYMBOL_PREDEFINED, SYMBOL_STR,
    SourceFileIndex, TAG_FULL_SPAN, TAG_PARTIAL_SPAN,
};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash, StableCrateId};
use rustc_middle::{
    implement_ty_decoder,
    ty::{Ty, TyCtxt, codec::TyDecoder},
};
use rustc_serialize::{
    Decodable, Decoder,
    opaque::{IntEncodedWithFixedSize, MemDecoder},
};
use rustc_span::{
    BytePos, ByteSymbol, DUMMY_SP, ExpnData, ExpnHash, ExpnId, SourceFile, Span, Symbol,
    SyntaxContext,
    hygiene::{HygieneDecodeContext, SyntaxContextKey},
};
use std::sync::Arc;

// This is only safe to decode the metadata of a single crate or the `ty_rcache` might confuse shorthands (see #360)
pub struct MetadataDecoder<'a, 'tcx> {
    opaque: MemDecoder<'a>,
    tcx: TyCtxt<'tcx>,
    ty_rcache: FxHashMap<usize, Ty<'tcx>>,
    file_index_to_file: FxHashMap<SourceFileIndex, Arc<SourceFile>>,
    file_index_to_stable_id: FxHashMap<SourceFileIndex, EncodedSourceFileId>,
    syntax_contexts: &'a FxHashMap<u32, AbsoluteBytePos>,
    expn_data: FxHashMap<(StableCrateId, u32), AbsoluteBytePos>,
    hygiene_context: &'a HygieneDecodeContext,
}

impl<'a, 'tcx> MetadataDecoder<'a, 'tcx> {
    fn file_index_to_file(&mut self, index: SourceFileIndex) -> Arc<SourceFile> {
        self.file_index_to_file
            .entry(index)
            .or_insert_with(|| {
                let source_file_id = &self.file_index_to_stable_id[&index];
                let source_file_cnum =
                    self.tcx.stable_crate_id_to_crate_num(source_file_id.stable_crate_id);

                self.tcx.import_source_files(source_file_cnum);
                self.tcx
                    .sess
                    .source_map()
                    .source_file_by_stable_id(source_file_id.stable_source_file_id)
                    .expect("failed to lookup `SourceFile` in new context")
            })
            .clone()
    }

    fn decode_symbol_or_byte_symbol<S>(
        &mut self,
        new: impl Fn(u32) -> S,
        read_and_intern_this: impl Fn(&mut Self) -> S,
        read_and_intern_opaque: impl Fn(&mut MemDecoder<'a>) -> S,
    ) -> S {
        let tag = self.read_u8();

        match tag {
            SYMBOL_STR => read_and_intern_this(self),
            SYMBOL_OFFSET => {
                // read str offset
                let pos = self.read_usize();

                // move to str ofset and read
                let sym = self.opaque.with_position(pos, |d| read_and_intern_opaque(d));
                sym
            }
            SYMBOL_PREDEFINED => new(self.read_u32()),
            _ => unreachable!(),
        }
    }
}

implement_ty_decoder!(MetadataDecoder<'a, 'tcx>);

use rustc_span::{AttrId, SpanDecoder};
impl SpanDecoder for MetadataDecoder<'_, '_> {
    fn decode_span(&mut self) -> Span {
        let ctxt = SyntaxContext::decode(self);
        let tag: u8 = Decodable::decode(self);

        if tag == TAG_PARTIAL_SPAN {
            return DUMMY_SP.with_ctxt(ctxt);
        }

        debug_assert!(tag == TAG_FULL_SPAN);

        let source_file_index = SourceFileIndex::decode(self);

        let lo = BytePos::decode(self);
        let len = BytePos::decode(self);

        let file = self.file_index_to_file(source_file_index);
        let lo = file.start_pos + lo;
        let hi = lo + len;

        Span::new(lo, hi, ctxt, None)
    }

    fn decode_symbol(&mut self) -> Symbol {
        self.decode_symbol_or_byte_symbol(
            Symbol::new,
            |this| Symbol::intern(this.read_str()),
            |opaque| Symbol::intern(opaque.read_str()),
        )
    }
    fn decode_byte_symbol(&mut self) -> rustc_span::ByteSymbol {
        self.decode_symbol_or_byte_symbol(
            ByteSymbol::new,
            |this| ByteSymbol::intern(this.read_byte_str()),
            |opaque| ByteSymbol::intern(opaque.read_byte_str()),
        )
    }
    fn decode_expn_id(&mut self) -> ExpnId {
        let stable_id = StableCrateId::decode(self);
        let cnum = self.tcx.stable_crate_id_to_crate_num(stable_id);
        let index = u32::decode(self);

        let expn_id = rustc_span::hygiene::decode_expn_id(cnum, index, |_| {
            let pos = self.expn_data.get(&(stable_id, index)).unwrap();
            self.with_position(pos.to_usize(), |decoder| {
                let data = ExpnData::decode(decoder);
                let hash = ExpnHash::decode(decoder);
                (data, hash)
            })
        });
        expn_id
    }
    fn decode_syntax_context(&mut self) -> SyntaxContext {
        let syntax_contexts = self.syntax_contexts;
        rustc_span::hygiene::decode_syntax_context(self, &self.hygiene_context, |this, id| {
            // This closure is invoked if we haven't already decoded the data for the `SyntaxContext` we are deserializing.
            // We look up the position of the associated `SyntaxData` and decode it.
            let pos = syntax_contexts.get(&id).unwrap();
            this.with_position(pos.to_usize(), |decoder| SyntaxContextKey::decode(decoder))
        })
    }
    fn decode_crate_num(&mut self) -> CrateNum {
        let stable_id = StableCrateId::decode(self);
        self.tcx.stable_crate_id_to_crate_num(stable_id)
    }
    fn decode_def_index(&mut self) -> DefIndex {
        panic!("trying to decode `DefIndex` outside the context of a `DefId`")
    }

    // Both the `CrateNum` and the `DefIndex` of a `DefId` can change in between two
    // compilation sessions. We use the `DefPathHash`, which is stable across
    // sessions, to map the old `DefId` to the new one.
    fn decode_def_id(&mut self) -> DefId {
        let def_path_hash = DefPathHash::decode(self);
        self.tcx.def_path_hash_to_def_id(def_path_hash).expect("Cannot resolve crate.")
    }

    fn decode_attr_id(&mut self) -> AttrId {
        todo!()
    }
}

impl<'a, 'tcx> TyDecoder<'tcx> for MetadataDecoder<'a, 'tcx> {
    // Whether crate-local information can be cleared while encoding
    const CLEAR_CROSS_CRATE: bool = true;

    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
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
        let new_decoder = self.opaque.split_at(pos);
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
        let mut decoder = MemDecoder::new(blob, 0).unwrap();
        let footer_pos = decoder
            .with_position(decoder.len() - IntEncodedWithFixedSize::ENCODED_SIZE, |d| {
                IntEncodedWithFixedSize::decode(d).0 as usize
            });
        decoder.with_position(footer_pos, |d| Footer::decode(d))
    };

    let mut decoder = MetadataDecoder {
        opaque: MemDecoder::new(blob, 0).unwrap(),
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
