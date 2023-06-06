use crate::{
    AbsoluteBytePos, EncodedSourceFileId, Footer, SourceFileIndex, SYMBOL_OFFSET,
    SYMBOL_PREINTERNED, SYMBOL_STR, TAG_FULL_SPAN, TAG_PARTIAL_SPAN,
};
use rustc_data_structures::{fx::FxHashMap, sync::Lrc};
use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use rustc_middle::{
    dep_graph::DepContext,
    ty::{self, codec::TyEncoder, PredicateKind, Ty, TyCtxt},
};
use rustc_serialize::{
    opaque::{FileEncoder, IntEncodedWithFixedSize},
    Encodable, Encoder,
};
use rustc_span::{
    hygiene::{raw_encode_syntax_context, HygieneEncodeContext},
    ExpnId, SourceFile, Span, Symbol, SyntaxContext,
};
use std::{collections::hash_map::Entry, io::Error, path::Path};

pub struct MetadataEncoder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    pub opaque: FileEncoder,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<PredicateKind<'tcx>, usize>,
    file_to_file_index: FxHashMap<*const SourceFile, SourceFileIndex>,
    hygiene_context: &'a HygieneEncodeContext,
    symbol_table: FxHashMap<Symbol, usize>,
}

impl<'a, 'tcx> MetadataEncoder<'a, 'tcx> {
    pub fn finish(self) -> Result<usize, Error> {
        self.opaque.finish()
    }

    fn source_file_index(&mut self, source_file: Lrc<SourceFile>) -> SourceFileIndex {
        self.file_to_file_index[&(&*source_file as *const SourceFile)]
    }
}

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) -> () {
            self.opaque.$name(value)
        })*
    }
}
impl<'a, 'tcx> Encoder for MetadataEncoder<'a, 'tcx> {
    encoder_methods! {
        emit_usize(usize);
        emit_u128(u128);
        emit_u64(u64);
        emit_u32(u32);
        emit_u16(u16);
        emit_u8(u8);

        emit_isize(isize);
        emit_i128(i128);
        emit_i64(i64);
        emit_i32(i32);
        emit_i16(i16);
        emit_i8(i8);

        emit_bool(bool);
        emit_char(char);
        emit_str(&str);
        emit_raw_bytes(&[u8]);
    }
}

impl<'a, 'tcx> Encodable<MetadataEncoder<'a, 'tcx>> for DefId {
    fn encode(&self, s: &mut MetadataEncoder<'a, 'tcx>) {
        s.tcx.def_path_hash(*self).encode(s)
    }
}

impl<'a, 'tcx> Encodable<MetadataEncoder<'a, 'tcx>> for CrateNum {
    fn encode(&self, s: &mut MetadataEncoder<'a, 'tcx>) {
        s.tcx.stable_crate_id(*self).encode(s)
    }
}

impl<'a, 'tcx> Encodable<MetadataEncoder<'a, 'tcx>> for DefIndex {
    fn encode(&self, _: &mut MetadataEncoder<'a, 'tcx>) {
        panic!("encoding `DefIndex` without context");
    }
}

impl<'a, 'tcx> Encodable<MetadataEncoder<'a, 'tcx>> for SyntaxContext {
    fn encode(&self, s: &mut MetadataEncoder<'a, 'tcx>) {
        raw_encode_syntax_context(*self, &s.hygiene_context, s);
    }
}

impl<'a, 'tcx> Encodable<MetadataEncoder<'a, 'tcx>> for ExpnId {
    fn encode(&self, s: &mut MetadataEncoder<'a, 'tcx>) {
        s.hygiene_context.schedule_expn_data_for_encoding(*self);
        self.krate.encode(s);
        self.local_id.as_u32().encode(s);
    }
}

impl<'a, 'tcx> Encodable<MetadataEncoder<'a, 'tcx>> for Span {
    fn encode(&self, s: &mut MetadataEncoder<'a, 'tcx>) {
        let span = self.data();
        span.ctxt.encode(s);

        if span.is_dummy() {
            return TAG_PARTIAL_SPAN.encode(s);
        }

        let source_file = s.tcx.sess().source_map().lookup_source_file(span.lo);
        if !source_file.contains(span.hi) {
            // Unfortunately, macro expansion still sometimes generates Spans
            // that malformed in this way.
            return TAG_PARTIAL_SPAN.encode(s);
        }

        let lo = span.lo - source_file.start_pos;
        let len = span.hi - span.lo;
        let source_file_index = s.source_file_index(source_file);

        TAG_FULL_SPAN.encode(s);
        source_file_index.encode(s);
        lo.encode(s);
        len.encode(s);
    }
}

impl<'a, 'tcx> Encodable<MetadataEncoder<'a, 'tcx>> for Symbol {
    fn encode(&self, s: &mut MetadataEncoder<'a, 'tcx>) {
        // if symbol preinterned, emit tag and symbol index
        if self.is_preinterned() {
            s.opaque.emit_u8(SYMBOL_PREINTERNED);
            s.opaque.emit_u32(self.as_u32());
        } else {
            // otherwise write it as string or as offset to it
            match s.symbol_table.entry(*self) {
                Entry::Vacant(o) => {
                    s.opaque.emit_u8(SYMBOL_STR);
                    let pos = s.opaque.position();
                    o.insert(pos);
                    s.emit_str(self.as_str());
                }
                Entry::Occupied(o) => {
                    let x = *o.get();
                    s.emit_u8(SYMBOL_OFFSET);
                    s.emit_usize(x);
                }
            }
        }
    }
}

impl<'a, 'tcx> TyEncoder for MetadataEncoder<'a, 'tcx> {
    type I = TyCtxt<'tcx>;

    // Whether crate-local information can be cleared while encoding
    const CLEAR_CROSS_CRATE: bool = true;

    fn position(&self) -> usize {
        self.opaque.position()
    }

    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, _alloc_id: &rustc_middle::mir::interpret::AllocId) {
        unimplemented!("encode_alloc_id")
    }
}

pub fn encode_metadata<'tcx, T: for<'a> Encodable<MetadataEncoder<'a, 'tcx>>>(
    tcx: TyCtxt<'tcx>,
    path: &Path,
    x: T,
) -> Result<(), Error> {
    let (file_to_file_index, file_index_to_stable_id) = {
        let files = tcx.sess.source_map().files();
        let mut file_to_file_index =
            FxHashMap::with_capacity_and_hasher(files.len(), Default::default());
        let mut file_index_to_stable_id =
            FxHashMap::with_capacity_and_hasher(files.len(), Default::default());

        for (index, file) in files.iter().enumerate() {
            let index = SourceFileIndex(index as u32);
            let file_ptr: *const SourceFile = &**file as *const _;
            file_to_file_index.insert(file_ptr, index);
            let source_file_id = EncodedSourceFileId::new(tcx, &file);
            file_index_to_stable_id.insert(index, source_file_id);
        }

        (file_to_file_index, file_index_to_stable_id)
    };

    let hygiene_context = HygieneEncodeContext::default();

    let mut encoder = MetadataEncoder {
        tcx,
        opaque: FileEncoder::new(path)?,
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
        hygiene_context: &hygiene_context,
        symbol_table: Default::default(),
        file_to_file_index,
    };
    x.encode(&mut encoder);

    let mut syntax_contexts = FxHashMap::default();
    let mut expn_data = FxHashMap::default();

    // Encode all hygiene data (`SyntaxContextData` and `ExpnData`) from the current
    // session.

    encoder.hygiene_context.encode(
        &mut encoder,
        |encoder, index, ctxt_data| {
            let pos = AbsoluteBytePos::new(encoder.position());
            ctxt_data.encode(encoder);
            syntax_contexts.insert(index, pos);
        },
        |encoder, expn_id, data, hash| {
            let pos = AbsoluteBytePos::new(encoder.position());
            data.encode(encoder);
            hash.encode(encoder);
            expn_data.insert((tcx.stable_crate_id(expn_id.krate), expn_id.local_id.as_u32()), pos);
        },
    );

    // Encode the file footer.
    let footer_pos = encoder.position() as u64;
    let footer = Footer { file_index_to_stable_id, syntax_contexts, expn_data };
    footer.encode(&mut encoder);

    // Encode the position of the footer as the last 8 bytes of the
    // file so we know where to look for it.
    IntEncodedWithFixedSize(footer_pos).encode(&mut encoder.opaque);

    // DO NOT WRITE ANYTHING TO THE ENCODER AFTER THIS POINT! The address
    // of the footer must be the last thing in the data stream.

    encoder.finish()?;
    Ok(())
}
