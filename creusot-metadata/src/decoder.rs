use rustc_data_structures::{
    fx::FxHashMap,
    owning_ref::OwningRef,
    rustc_erase_owner,
    sync::{Lrc, MetadataRef},
};
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash, StableCrateId};
use rustc_middle::{
    implement_ty_decoder,
    ty::{codec::TyDecoder, Ty, TyCtxt},
};
use rustc_serialize::opaque;
pub use rustc_serialize::{Decodable, Decoder};
use rustc_span::{BytePos, FileName, Span, SyntaxContext};
use std::{fs::File, io::Read, path::Path};

// copied from rustc
#[derive(Clone)]
pub struct MetadataBlob(pub Lrc<MetadataRef>);

impl MetadataBlob {
    pub fn from_file(path: &Path) -> Result<Self, std::io::Error> {
        let mut encoded = Vec::new();
        let mut file = File::open(path)?;
        file.read_to_end(&mut encoded)?;

        let encoded_owned = OwningRef::new(encoded);
        let metadat_ref: OwningRef<Box<_>, [u8]> = encoded_owned.map_owner_box();
        Ok(MetadataBlob(Lrc::new(rustc_erase_owner!(metadat_ref))))
    }
}

// This is only safe to decode the metadata of a single crate or the `ty_rcache` might confuse shorthands (see #360)
pub struct MetadataDecoder<'a, 'tcx> {
    opaque: opaque::MemDecoder<'a>,
    tcx: TyCtxt<'tcx>,
    ty_rcache: FxHashMap<usize, Ty<'tcx>>,
}

impl<'a, 'tcx> MetadataDecoder<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, blob: &'a MetadataBlob) -> Self {
        MetadataDecoder {
            opaque: opaque::MemDecoder::new(&blob.0, 0),
            tcx,
            ty_rcache: Default::default(),
        }
    }

    // From rustc
    fn def_path_hash_to_def_id(&self, hash: DefPathHash) -> DefId {
        self.tcx.def_path_hash_to_def_id(hash, &mut || panic!("testxxx"))
    }
}

// the following two instances are from rustc
// This impl makes sure that we get a runtime error when we try decode a
// `DefIndex` that is not contained in a `DefId`. Such a case would be problematic
// because we would not know how to transform the `DefIndex` to the current
// context.
impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for DefIndex {
    fn decode(_: &mut MetadataDecoder<'a, 'tcx>) -> DefIndex {
        panic!("trying to decode `DefIndex` outside the context of a `DefId`")
    }
}

// Both the `CrateNum` and the `DefIndex` of a `DefId` can change in between two
// compilation sessions. We use the `DefPathHash`, which is stable across
// sessions, to map the old `DefId` to the new one.
impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for DefId {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> Self {
        let def_path_hash = DefPathHash::decode(d);
        d.def_path_hash_to_def_id(def_path_hash)
    }
}

impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for CrateNum {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> CrateNum {
        let stable_id = StableCrateId::decode(d);
        d.tcx.stable_crate_id_to_crate_num(stable_id)
    }
}

impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for Span {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> Span {
        // let ctxt = SyntaxContext::decode(d);
        let lo = BytePos::decode(d);
        let len = BytePos::decode(d);
        let hi = lo + len;

        use rustc_span::RealFileName;
        let name = <Option<RealFileName>>::decode(d);

        let source_map = d.tcx.sess.source_map();

        let start_pos = match name {
            Some(rname) => source_map.load_file(rname.local_path_if_available()).unwrap().start_pos,
            None => BytePos(0),
        };

        let lo = lo + start_pos;
        let hi = hi + start_pos;

        // Do not try to decode parent for foreign spans.
        Span::new(lo, hi, SyntaxContext::root(), None)
    }
}

implement_ty_decoder!(MetadataDecoder<'a, 'tcx>);

impl<'a, 'tcx> TyDecoder for MetadataDecoder<'a, 'tcx> {
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
        let new_opaque = opaque::MemDecoder::new(self.opaque.data, pos);
        let old_opaque = std::mem::replace(&mut self.opaque, new_opaque);
        let r = f(self);
        self.opaque = old_opaque;
        r
    }

    fn decode_alloc_id(&mut self) -> rustc_middle::mir::interpret::AllocId {
        unimplemented!("decode_alloc_id")
    }
}
