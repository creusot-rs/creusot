use crate::{
    ctx::Erased,
    translation::{external::ExternSpec, pearlite::ScopedTerm},
    validate::AnfBlock,
};
use creusot_metadata::{decode_metadata, encode_metadata};
use indexmap::IndexMap;
use once_map::unsync::OnceMap;
use rustc_hir::def_id::{CrateNum, DefId, DefPathHash, LOCAL_CRATE, LocalDefId};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::OutputType;
use rustc_span::Symbol;
use std::{
    collections::{HashMap, HashSet},
    fs::File,
    io::Read,
    path::{Path, PathBuf},
};

type ExternSpecs<'tcx> = HashMap<DefId, ExternSpec<'tcx>>;

// TODO: this should lazily load the metadata.
#[derive(Default)]
pub struct Metadata<'tcx> {
    crates: HashMap<CrateNum, CrateMetadata<'tcx>>,
    extern_specs: ExternSpecs<'tcx>,
    erased_thir: HashMap<DefId, AnfBlock<'tcx>>,
    erased_defid: HashMap<DefId, Erased<'tcx>>,
}

impl<'tcx> Metadata<'tcx> {
    pub(crate) fn get(&self, cnum: CrateNum) -> Option<&CrateMetadata<'tcx>> {
        self.crates.get(&cnum)
    }

    pub(crate) fn term(&self, def_id: DefId) -> Option<&ScopedTerm<'tcx>> {
        assert!(!def_id.is_local());
        self.get(def_id.krate)?.term(def_id)
    }

    pub(crate) fn params_open_inv(&self, def_id: DefId) -> Option<&Vec<usize>> {
        assert!(!def_id.is_local());
        self.get(def_id.krate)?.params_open_inv(def_id)
    }

    pub(crate) fn creusot_item(&self, sym: Symbol) -> Option<DefId> {
        for cmeta in &self.crates {
            if cmeta.1.creusot_item(sym).is_some() {
                return cmeta.1.creusot_item(sym);
            }
        }
        None
    }

    pub(crate) fn extern_spec(&self, id: DefId) -> Option<&ExternSpec<'tcx>> {
        self.extern_specs.get(&id)
    }

    pub(crate) fn erased_thir(&self, id: DefId) -> Option<&AnfBlock<'tcx>> {
        self.erased_thir.get(&id)
    }

    pub(crate) fn erasure(&self, id: DefId) -> Option<&Erased<'tcx>> {
        self.erased_defid.get(&id)
    }

    pub(crate) fn load(&mut self, tcx: TyCtxt<'tcx>, overrides: &HashMap<String, PathBuf>) {
        for cnum in external_crates(tcx) {
            let Some((cmeta, ext_specs, erased_thir, erased_defid)) =
                CrateMetadata::load(tcx, overrides, cnum)
            else {
                continue;
            };
            self.crates.insert(cnum, cmeta);
            for (id, spec) in ext_specs.into_iter() {
                if self.extern_specs.insert(id, spec).is_some() {
                    panic!("duplicate external spec found for {:?} while loading {:?}", id, cnum);
                }
            }
            for (id, erased) in erased_thir {
                self.erased_thir.insert(id, erased);
            }
            for (id, erased) in erased_defid {
                self.erased_defid.insert(id, erased);
            }
        }
    }
}

pub struct CrateMetadata<'tcx> {
    terms: IndexMap<DefId, ScopedTerm<'tcx>>,
    creusot_items: HashMap<Symbol, DefId>,
    params_open_inv: HashMap<DefId, Vec<usize>>,
}

impl<'tcx> CrateMetadata<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            terms: Default::default(),
            creusot_items: Default::default(),
            params_open_inv: Default::default(),
        }
    }

    pub(crate) fn term(&self, def_id: DefId) -> Option<&ScopedTerm<'tcx>> {
        assert!(!def_id.is_local());
        self.terms.get(&def_id)
    }

    pub(crate) fn params_open_inv(&self, def_id: DefId) -> Option<&Vec<usize>> {
        assert!(!def_id.is_local());
        self.params_open_inv.get(&def_id)
    }

    pub(crate) fn creusot_item(&self, sym: Symbol) -> Option<DefId> {
        self.creusot_items.get(&sym).cloned()
    }

    fn load(
        tcx: TyCtxt<'tcx>,
        overrides: &HashMap<String, PathBuf>,
        cnum: CrateNum,
    ) -> Option<(Self, ExternSpecs<'tcx>, Vec<(DefId, AnfBlock<'tcx>)>, Vec<(DefId, Erased<'tcx>)>)>
    {
        let binary_path = creusot_metadata_path(tcx, overrides, cnum);
        let metadata = load_binary_metadata(tcx, cnum, &binary_path)?;

        let mut meta = CrateMetadata::new();

        for (def_id, summary) in metadata.terms.into_iter() {
            meta.terms.insert(def_id, summary);
        }

        meta.creusot_items = metadata.creusot_items;
        meta.params_open_inv = metadata.params_open_inv;

        Some((meta, metadata.extern_specs, metadata.erased_thir, metadata.erased_defid))
    }
}

// We use this type to perform (de)serialization of metadata because for annoying
// `extern crate` related reasons we cannot use the instance of `TyEncodable` / `TyDecodable`
// for `IndexMap`. Instead, we flatten it to a association list and then convert that into
// a proper index map after parsing.
#[derive(TyDecodable, TyEncodable)]
pub(crate) struct BinaryMetadata<'tcx> {
    terms: Vec<(DefId, ScopedTerm<'tcx>)>,
    creusot_items: HashMap<Symbol, DefId>,
    extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
    params_open_inv: HashMap<DefId, Vec<usize>>,
    erased_thir: Vec<(DefId, AnfBlock<'tcx>)>,
    erased_defid: Vec<(DefId, Erased<'tcx>)>,
}

impl<'tcx> BinaryMetadata<'tcx> {
    pub(crate) fn from_parts(
        mut terms: OnceMap<DefId, Box<Option<ScopedTerm<'tcx>>>>,
        creusot_items: HashMap<Symbol, DefId>,
        extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
        params_open_inv: HashMap<DefId, Vec<usize>>,
        erased_thir: Vec<(DefId, AnfBlock<'tcx>)>,
        erased_defid: Vec<(DefId, Erased<'tcx>)>,
    ) -> Self {
        let terms = terms
            .iter_mut()
            .filter(|(def_id, t)| def_id.is_local() && t.is_some())
            .map(|(id, t)| (*id, t.clone().unwrap()))
            .collect();
        BinaryMetadata {
            terms,
            creusot_items,
            extern_specs,
            params_open_inv,
            erased_thir,
            erased_defid,
        }
    }

    pub(crate) fn without_specs(erased_thir: Vec<(DefId, AnfBlock<'tcx>)>) -> Self {
        BinaryMetadata {
            terms: Vec::new(),
            creusot_items: HashMap::new(),
            extern_specs: HashMap::new(),
            params_open_inv: HashMap::new(),
            erased_thir,
            erased_defid: Vec::new(),
        }
    }
}

pub(crate) fn dump_exports<'tcx>(
    tcx: TyCtxt<'tcx>,
    overrides: &HashMap<String, PathBuf>,
    metadata: BinaryMetadata<'tcx>,
) {
    let out_filename = creusot_metadata_path(tcx, overrides, LOCAL_CRATE);
    debug!("dump_exports={:?}", out_filename);
    encode_metadata(tcx, &out_filename, metadata).unwrap_or_else(|err| {
        panic!("could not save metadata path=`{:?}` error={}", out_filename, err)
    });
}

fn load_binary_metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    cnum: CrateNum,
    path: &Path,
) -> Option<BinaryMetadata<'tcx>> {
    let mut blob = Vec::new();
    match File::open(path).and_then(|mut file| file.read_to_end(&mut blob)) {
        Ok(_) => (),
        Err(e) => {
            warn!("could not read metadata for crate `{:?}`: {:?}", tcx.crate_name(cnum), e);
            return None;
        }
    }

    Some(decode_metadata(tcx, &blob))
}

fn creusot_metadata_path(
    tcx: TyCtxt,
    overrides: &HashMap<String, PathBuf>,
    cnum: CrateNum,
) -> PathBuf {
    if let Some(path) = overrides.get(&tcx.crate_name(cnum).to_string()) {
        debug!("loading crate {:?} from override path", cnum);
        path.clone()
    } else if cnum == LOCAL_CRATE {
        let outputs = tcx.output_filenames(());
        let out = outputs.path(OutputType::Metadata);
        out.as_path().to_owned().with_extension("cmeta")
    } else {
        let cs = tcx.used_crate_source(cnum);
        cs.paths().next().unwrap().with_extension("cmeta")
    }
}

fn external_crates(tcx: TyCtxt<'_>) -> Vec<CrateNum> {
    let mut deps = Vec::new();
    for cr in tcx.crates(()) {
        if *cr != LOCAL_CRATE {
            deps.push(*cr);
        }
    }
    deps
}

pub fn get_erasure_required(tcx: TyCtxt, erasure_check_dir: &Path) -> HashSet<LocalDefId> {
    let mut required = HashSet::new();
    let Ok(dir) = std::fs::read_dir(erasure_check_dir) else {
        return required;
    };
    for entry in dir {
        let Ok(entry) = entry else {
            continue;
        };
        let Ok(more_required) = decode_local_def_ids(tcx, &entry.path()) else { continue };
        required.extend(more_required);
    }
    required
}

/// We don't want to go through the `Encodable`/`Decodable` for `DefId` because
/// decoding only works if the `DefId`'s `CrateNum` is in a dependency of the current crate,
/// whereas we are planning to read these `DefId`s in a fresh compilation session.
///
/// Instead, we explicitly convert `DefId` to `DefPathHash` and serialize that.
/// When deserializing, we only care about IDs from the current crate (`LocalDefId`).
pub fn encode_def_ids<'a>(
    tcx: TyCtxt,
    path: &Path,
    def_ids: impl IntoIterator<Item = &'a DefId>,
) -> Result<(), std::io::Error> {
    let hashes: Vec<DefPathHash> =
        def_ids.into_iter().map(|def_id| tcx.def_path_hash(*def_id)).collect();
    encode_metadata(tcx, path, hashes)
}

/// Skip `DefId`s from other crates
fn decode_local_def_ids(tcx: TyCtxt, file: &Path) -> Result<Vec<LocalDefId>, std::io::Error> {
    let contents = std::fs::read(file)?;
    let hashes: Vec<DefPathHash> = decode_metadata(tcx, &contents);
    Ok(hashes.into_iter().filter_map(|hash| def_path_hash_to_local_id(tcx, hash)).collect())
}

/// Only try to decode `LocalDefId`s
fn def_path_hash_to_local_id(tcx: TyCtxt, hash: DefPathHash) -> Option<LocalDefId> {
    if hash.stable_crate_id() == tcx.stable_crate_id(LOCAL_CRATE) {
        tcx.definitions_untracked().local_def_path_hash_to_def_id(hash)
    } else {
        None
    }
}
