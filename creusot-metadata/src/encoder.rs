use crate::{
    AbsoluteBytePos, EncodedSourceFileId, Footer, SYMBOL_OFFSET, SYMBOL_PREDEFINED, SYMBOL_STR,
    SourceFileIndex, TAG_FULL_SPAN, TAG_PARTIAL_SPAN,
};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use rustc_middle::{
    dep_graph::DepContext,
    ty::{self, PredicateKind, Ty, TyCtxt, codec::TyEncoder},
};
use rustc_serialize::{
    Encodable, Encoder,
    opaque::{FileEncoder, IntEncodedWithFixedSize},
};
use rustc_span::{
    ExpnId, SourceFile, Span, Symbol, SyntaxContext,
    hygiene::{HygieneEncodeContext, raw_encode_syntax_context},
};
use std::{
    collections::hash_map::Entry,
    io::Error,
    path::{Path, PathBuf},
    sync::Arc,
};

pub struct MetadataEncoder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    pub opaque: FileEncoder,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<PredicateKind<'tcx>, usize>,
    file_to_file_index: FxHashMap<*const SourceFile, SourceFileIndex>,
    hygiene_context: &'a HygieneEncodeContext,
    symbol_index_table: FxHashMap<u32, usize>,
}

impl<'a, 'tcx> MetadataEncoder<'a, 'tcx> {
    pub fn finish(mut self) -> Result<usize, (PathBuf, Error)> {
        self.opaque.finish()
    }

    fn source_file_index(&mut self, source_file: Arc<SourceFile>) -> SourceFileIndex {
        self.file_to_file_index[&(&*source_file as *const SourceFile)]
    }

    fn encode_symbol_or_byte_symbol(
        &mut self,
        index: u32,
        emit_str_or_byte_str: impl Fn(&mut Self),
    ) {
        // if symbol preinterned, emit tag and symbol index
        if Symbol::is_predefined(index) {
            self.opaque.emit_u8(SYMBOL_PREDEFINED);
            self.opaque.emit_u32(index);
        } else {
            // otherwise write it as string or as offset to it
            match self.symbol_index_table.entry(index) {
                Entry::Vacant(o) => {
                    self.opaque.emit_u8(SYMBOL_STR);
                    let pos = self.opaque.position();
                    o.insert(pos);
                    emit_str_or_byte_str(self);
                }
                Entry::Occupied(o) => {
                    let x = *o.get();
                    self.emit_u8(SYMBOL_OFFSET);
                    self.emit_usize(x);
                }
            }
        }
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

use rustc_span::SpanEncoder;
impl SpanEncoder for MetadataEncoder<'_, '_> {
    fn encode_span(&mut self, span: Span) {
        let span = span.data();
        span.ctxt.encode(self);

        if span.is_dummy() {
            return TAG_PARTIAL_SPAN.encode(self);
        }

        let source_file = self.tcx.sess().source_map().lookup_source_file(span.lo);
        if !source_file.contains(span.hi) {
            // Unfortunately, macro expansion still sometimes generates Spans
            // that malformed in this way.
            return TAG_PARTIAL_SPAN.encode(self);
        }

        let lo = span.lo - source_file.start_pos;
        let len = span.hi - span.lo;
        let source_file_index = self.source_file_index(source_file);

        TAG_FULL_SPAN.encode(self);
        source_file_index.encode(self);
        lo.encode(self);
        len.encode(self);
    }
    fn encode_symbol(&mut self, sym: Symbol) {
        self.encode_symbol_or_byte_symbol(sym.as_u32(), |this| this.emit_str(sym.as_str()));
    }
    fn encode_byte_symbol(&mut self, sym: rustc_span::ByteSymbol) {
        self.encode_symbol_or_byte_symbol(sym.as_u32(), |this| {
            this.emit_byte_str(sym.as_byte_str())
        });
    }
    fn encode_expn_id(&mut self, eid: ExpnId) {
        self.hygiene_context.schedule_expn_data_for_encoding(eid);
        eid.krate.encode(self);
        eid.local_id.as_u32().encode(self);
    }
    fn encode_syntax_context(&mut self, ctx: SyntaxContext) {
        raw_encode_syntax_context(ctx, &self.hygiene_context, self);
    }
    fn encode_crate_num(&mut self, cnum: CrateNum) {
        self.tcx.stable_crate_id(cnum).encode(self)
    }
    fn encode_def_index(&mut self, _: DefIndex) {
        panic!("encoding `DefIndex` without context");
    }
    fn encode_def_id(&mut self, id: DefId) {
        self.tcx.def_path_hash(id).encode(self)
    }
}

impl<'a, 'tcx> TyEncoder<'tcx> for MetadataEncoder<'a, 'tcx> {
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
) -> Result<(), (PathBuf, Error)> {
    let (file_to_file_index, file_index_to_stable_id) = {
        let files = tcx.sess.source_map().files();
        let mut file_to_file_index =
            FxHashMap::with_capacity_and_hasher(files.len(), Default::default());
        let mut file_index_to_stable_id =
            FxHashMap::with_capacity_and_hasher(files.len(), Default::default());
        use rustc_span::def_id::LOCAL_CRATE;
        let source_map = tcx.sess.source_map();
        let working_directory = &tcx.sess.opts.working_dir;
        let local_crate_stable_id = tcx.stable_crate_id(LOCAL_CRATE);

        // This portion of the code is adapted from the rustc metadata encoder, while the rest of
        // the code in this file is based off the rustc incremental cache encoder.
        //
        // Probably we should refactor the code to be exclusively based on the metadata encoder
        for (index, file) in files.iter().enumerate() {
            let index = SourceFileIndex(index as u32);
            let file_ptr: *const SourceFile = &**file as *const _;
            file_to_file_index.insert(file_ptr, index);

            let mut adapted_source_file = (**file).clone();
            if adapted_source_file.cnum == LOCAL_CRATE {
                use rustc_span::FileName;
                match file.name {
                    FileName::Real(ref original_file_name) => {
                        let adapted_file_name =
                            source_map.path_mapping().to_embeddable_absolute_path(
                                original_file_name.clone(),
                                working_directory,
                            );

                        adapted_source_file.name = FileName::Real(adapted_file_name);
                    }
                    _ => {
                        // expanded code, not from a file
                    }
                };
                use rustc_span::StableSourceFileId;
                adapted_source_file.stable_id = StableSourceFileId::from_filename_for_export(
                    &adapted_source_file.name,
                    local_crate_stable_id,
                );
            }

            let source_file_id = EncodedSourceFileId::new(tcx, &adapted_source_file);
            file_index_to_stable_id.insert(index, source_file_id);
        }

        (file_to_file_index, file_index_to_stable_id)
    };

    let hygiene_context = HygieneEncodeContext::default();

    let mut encoder = MetadataEncoder {
        tcx,
        opaque: FileEncoder::new(path).unwrap(),
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
        hygiene_context: &hygiene_context,
        symbol_index_table: Default::default(),
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
