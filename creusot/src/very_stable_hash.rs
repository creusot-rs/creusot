use rustc_data_structures::stable_hasher::StableHasher;
use rustc_hashes::Hash64;
use rustc_hir::{
    def_id::{CrateNum, DefId},
    definitions::{DefPath, DefPathData, DisambiguatedDefPathData},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use std::hash::{Hash, Hasher};

// HashStable is not stable enough for our purposes
// of hashing ImplSubject to identify Rust impls in the output Coma:
// HashStable depends on the target platform (Linux/Mac/Windows).
//
// The remaining difference is how VeryStableHash hashes identifiers:
// - Symbol is hashed as a string (not as a pointer).
// - CrateNum is hashed as the crate name (not as a number).
// - DefId is hashed as a DefPath
pub trait VeryStableHash<CTX> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher);
}

pub fn get_very_stable_hash<CTX, T: VeryStableHash<CTX> + ?Sized>(t: &T, tcx: &CTX) -> Hash64 {
    let mut hcx = StableHasher::new();
    t.very_stable_hash(tcx, &mut hcx);
    hcx.finish::<Hash64>()
}

// Implementors

// Stdlib types

impl<CTX> VeryStableHash<CTX> for bool {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        hcx.write_u8(*self as u8);
    }
}

impl<CTX> VeryStableHash<CTX> for u32 {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        hcx.write_u32(*self);
    }
}

impl<CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for [T] {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        hcx.write_usize(self.len());
        for item in self {
            item.very_stable_hash(tcx, hcx);
        }
    }
}

impl<CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for Option<T> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            Some(x) => {
                x.very_stable_hash(tcx, hcx);
            }
            None => {}
        }
    }
}

impl<CTX, T: VeryStableHash<CTX>, E: VeryStableHash<CTX>> VeryStableHash<CTX> for Result<T, E> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            Ok(x) => {
                x.very_stable_hash(tcx, hcx);
            }
            Err(e) => {
                e.very_stable_hash(tcx, hcx);
            }
        }
    }
}

impl<CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for Vec<T> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.as_slice().very_stable_hash(tcx, hcx);
    }
}

// Rustc types

impl VeryStableHash<TyCtxt<'_>> for CrateNum {
    // Hash the name of the crate, not the number
    fn very_stable_hash(&self, tcx: &TyCtxt, hcx: &mut StableHasher) {
        tcx.crate_name(*self).very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for DefId {
    // Expand the DefId to a DefPath and hash the path
    fn very_stable_hash(&self, tcx: &TyCtxt, hcx: &mut StableHasher) {
        tcx.def_path(*self).very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for DefPath {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        self.krate.very_stable_hash(tcx, hcx);
        self.data.very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for Symbol {
    // Hash the string, not the pointer
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.as_str().hash(hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for DisambiguatedDefPathData {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.data.very_stable_hash(tcx, hcx);
        self.disambiguator.very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for DefPathData {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        use DefPathData::*;
        match self {
            CrateRoot
            | Impl
            | ForeignMod
            | Use
            | GlobalAsm
            | Closure
            | Ctor
            | AnonConst
            | OpaqueTy
            | SyntheticCoroutineBody
            | LateAnonConst
            | DesugaredAnonymousLifetime
            | NestedStatic => {}
            TypeNs(symbol)
            | ValueNs(symbol)
            | MacroNs(symbol)
            | LifetimeNs(symbol)
            | OpaqueLifetime(symbol)
            | AnonAssocTy(symbol) => symbol.very_stable_hash(tcx, hcx),
        }
    }
}
