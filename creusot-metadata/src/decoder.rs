use rustc_data_structures::owning_ref::OwningRef;
use rustc_data_structures::rustc_erase_owner;
use rustc_data_structures::sync::{Lrc, MetadataRef};
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, DefPathHash, StableCrateId};
use rustc_metadata::creader::CStore;
use rustc_middle::implement_ty_decoder;
use rustc_middle::middle::cstore::CrateStore;
use rustc_middle::ty;
use rustc_middle::ty::codec::TyDecoder;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_serialize::opaque;
pub use rustc_serialize::{Decodable, Decoder};
use std::fs::File;
use std::io::Read;
use std::path::Path;

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

pub struct MetadataDecoder<'a, 'tcx> {
    opaque: opaque::Decoder<'a>,
    cnum: CrateNum,
    tcx: TyCtxt<'tcx>,
}

impl MetadataDecoder<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, cnum: CrateNum, blob: &'a MetadataBlob) -> Self {
        MetadataDecoder { opaque: opaque::Decoder::new(&blob.0, 0), cnum, tcx }
    }

    // From rustc
    fn def_path_hash_to_def_id(&self, hash: DefPathHash) -> DefId {
        let stable_crate_id = hash.stable_crate_id();

        // If this is a DefPathHash from the local crate, we can look up the
        // DefId in the tcx's `Definitions`.
        if stable_crate_id == self.tcx.sess.local_stable_crate_id() {
            self.tcx.definitions_untracked().local_def_path_hash_to_def_id(hash).to_def_id()
        } else {
            // If this is a DefPathHash from an upstream crate, let the CrateStore map
            // it to a DefId.
            let cnum = self.tcx.stable_crate_id_to_crate_num(stable_crate_id);
            CStore::from_tcx(self.tcx).def_path_hash_to_def_id(cnum, hash)
        }
    }
}

// the following two instances are from rustc
// This impl makes sure that we get a runtime error when we try decode a
// `DefIndex` that is not contained in a `DefId`. Such a case would be problematic
// because we would not know how to transform the `DefIndex` to the current
// context.
impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for DefIndex {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> Result<DefIndex, String> {
        Err(d.error("trying to decode `DefIndex` outside the context of a `DefId`"))
    }
}

// Both the `CrateNum` and the `DefIndex` of a `DefId` can change in between two
// compilation sessions. We use the `DefPathHash`, which is stable across
// sessions, to map the old `DefId` to the new one.
impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for DefId {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> Result<Self, String> {
        let def_path_hash = DefPathHash::decode(d)?;
        Ok(d.def_path_hash_to_def_id(def_path_hash))
    }
}

impl<'a, 'tcx> Decodable<MetadataDecoder<'a, 'tcx>> for CrateNum {
    fn decode(d: &mut MetadataDecoder<'a, 'tcx>) -> Result<CrateNum, String> {
        let stable_id = StableCrateId::decode(d)?;
        Ok(d.tcx.stable_crate_id_to_crate_num(stable_id))
    }
}

implement_ty_decoder!(MetadataDecoder<'a, 'tcx>);

impl<'a, 'tcx> TyDecoder<'tcx> for MetadataDecoder<'a, 'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;

    #[inline]
    fn tcx(&self) -> TyCtxt<'tcx> {
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

    fn cached_ty_for_shorthand<F>(
        &mut self,
        shorthand: usize,
        or_insert_with: F,
    ) -> Result<Ty<'tcx>, Self::Error>
    where
        F: FnOnce(&mut Self) -> Result<Ty<'tcx>, Self::Error>,
    {
        let tcx = self.tcx();

        let key = ty::CReaderCacheKey { cnum: Some(self.cnum), pos: shorthand };

        if let Some(&ty) = tcx.ty_rcache.borrow().get(&key) {
            return Ok(ty);
        }

        let ty = or_insert_with(self)?;
        tcx.ty_rcache.borrow_mut().insert(key, ty);
        Ok(ty)
    }

    fn with_position<F, R>(&mut self, pos: usize, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let new_opaque = opaque::Decoder::new(self.opaque.data, pos);
        let old_opaque = std::mem::replace(&mut self.opaque, new_opaque);
        let r = f(self);
        self.opaque = old_opaque;
        r
    }

    fn decode_alloc_id(&mut self) -> Result<rustc_middle::mir::interpret::AllocId, Self::Error> {
        unimplemented!("decode_alloc_id")
    }
}
