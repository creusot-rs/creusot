use crate::creusot_items::CreusotItems;
use crate::ctx::*;
use crate::translation::specification::PreContract;
use creusot_metadata::decoder::{Decodable, MetadataBlob, MetadataDecoder};
use creusot_metadata::encoder::{Encodable, MetadataEncoder};
use indexmap::IndexMap;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_metadata::creader::CStore;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::TyCtxt;
use rustc_session::cstore::CrateStore;
use rustc_span::Symbol;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use why3::declaration::Module;

use super::specification::typing::Term;

type CloneMetadata<'tcx> = HashMap<DefId, CloneSummary<'tcx>>;
type ExternSpecs = HashMap<DefId, PreContract>;

// TODO: this should lazily load the metadata.
pub struct Metadata<'tcx> {
    tcx: TyCtxt<'tcx>,
    crates: HashMap<CrateNum, CrateMetadata<'tcx>>,
    extern_specs: ExternSpecs,
}

impl Metadata<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Metadata { tcx, crates: Default::default(), extern_specs: Default::default() }
    }

    pub fn get(&self, cnum: CrateNum) -> Option<&CrateMetadata<'tcx>> {
        self.crates.get(&cnum)
    }

    /// Determines whether a DefId has been verified by Creusot or not.
    /// We consider that if we don't have metadata about a crate then it must be unverified
    pub fn verified(&self, def_id: DefId) -> bool {
        self.crates.contains_key(&def_id.krate)
    }

    pub fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        assert!(!def_id.is_local());
        self.get(def_id.krate)?.dependencies.get(&def_id)
    }

    pub fn term(&self, def_id: DefId) -> Option<&Term<'tcx>> {
        assert!(!def_id.is_local());
        self.get(def_id.krate)?.terms.get(&def_id)
    }

    pub fn debug_creusot_items(&self) {
        for cmeta in &self.crates {
            error!("items {:?}", cmeta.0);

            eprintln!("{:?}", cmeta.1.creusot_items);
        }
    }

    pub fn creusot_item(&self, sym: Symbol) -> Option<DefId> {
        for cmeta in &self.crates {
            if cmeta.1.creusot_item(sym).is_some() {
                return cmeta.1.creusot_item(sym);
            }
        }
        return None;
    }

    pub fn extern_spec(&self, id: DefId) -> Option<&PreContract> {
        self.extern_specs.get(&id)
    }

    pub fn load(&mut self, overrides: &HashMap<String, String>) {
        let cstore = CStore::from_tcx(self.tcx);
        for cnum in external_crates(self.tcx) {
            let (cmeta, mut ext_specs) = CrateMetadata::load(self.tcx, cstore, overrides, cnum);
            self.crates.insert(cnum, cmeta);

            for (id, spec) in ext_specs.drain() {
                if let Some(_) = self.extern_specs.insert(id, spec) {
                    panic!("duplicate external spec found for {:?} while loading {:?}", id, cnum);
                }
            }
        }
    }
}

pub struct CrateMetadata<'tcx> {
    modules: IndexMap<DefId, Module>,
    terms: IndexMap<DefId, Term<'tcx>>,
    dependencies: CloneMetadata<'tcx>,
    creusot_items: CreusotItems,
    // extern_specs: HashMap<DefId, PreContract>,
}

impl CrateMetadata<'tcx> {
    pub fn new() -> Self {
        Self {
            modules: Default::default(),
            dependencies: Default::default(),
            terms: Default::default(),
            creusot_items: Default::default(),
            // extern_specs: Default::default(),
        }
    }

    pub fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        assert!(!def_id.is_local());
        self.dependencies.get(&def_id)
    }

    pub fn term(&self, def_id: DefId) -> Option<&Term<'tcx>> {
        assert!(!def_id.is_local());
        self.terms.get(&def_id)
    }

    pub fn body(&self, def_id: DefId) -> Option<&Module> {
        assert!(!def_id.is_local());
        self.modules.get(&def_id)
    }

    pub fn creusot_item(&self, sym: Symbol) -> Option<DefId> {
        self.creusot_items.symbol_to_id.get(&sym).cloned()
    }

    fn load(
        tcx: TyCtxt<'tcx>,
        cstore: &CStore,
        overrides: &HashMap<String, String>,
        cnum: CrateNum,
    ) -> (Self, ExternSpecs) {
        let mut meta = CrateMetadata::new();

        let base_path = creusot_metadata_base_path(cstore, overrides, cnum);

        let binary_path = creusot_metadata_binary_path(base_path.clone());

        let mut externs = Default::default();
        if let Some(metadata) = load_binary_metadata(tcx, cstore, cnum, &binary_path) {
            for (def_id, summary) in metadata.dependencies.into_iter() {
                meta.dependencies.insert(def_id, summary.into_iter().collect());
            }

            for (def_id, summary) in metadata.terms.into_iter() {
                meta.terms.insert(def_id, summary);
            }

            meta.creusot_items = metadata.creusot_items;

            externs = metadata.extern_specs;
        }

        (meta, externs)
    }
}

// We use this type to perform (de)serialization of metadata because for annoying
// `extern crate` related reasons we cannot use the instance of `TyEncodable` / `TyDecodable`
// for `IndexMap`. Instead, we flatten it to a association list and then convert that into
// a proper index map after parsing.
#[derive(TyDecodable, TyEncodable)]
pub struct BinaryMetadata<'tcx> {
    // Flatten the index map into a vector
    dependencies: HashMap<DefId, Vec<((DefId, SubstsRef<'tcx>), CloneInfo<'tcx>)>>,

    terms: Vec<(DefId, Term<'tcx>)>,

    creusot_items: CreusotItems,

    extern_specs: HashMap<DefId, PreContract>,
}

use rustc_middle::ty::Visibility;

impl BinaryMetadata<'tcx> {
    pub fn from_parts(
        tcx: TyCtxt<'tcx>,
        functions: &IndexMap<DefId, TranslatedItem<'tcx>>,
        terms: &IndexMap<DefId, Term<'tcx>>,
        items: &CreusotItems,
        extern_specs: &HashMap<DefId, PreContract>,
    ) -> Self {
        let dependencies = functions
            .iter()
            .filter(|(def_id, _)| {
                tcx.visibility(**def_id) == Visibility::Public && def_id.is_local()
            })
            .map(|(def_id, v)| (*def_id, v.local_dependencies().clone().into_iter().collect()))
            .collect();

        let terms = terms
            .iter()
            .filter(|(def_id, _)| def_id.is_local())
            .map(|(id, t)| (*id, t.clone()))
            .collect();

        BinaryMetadata {
            dependencies,
            terms,
            creusot_items: items.clone(),
            extern_specs: extern_specs.clone(),
        }
    }
}

fn export_file(ctx: &TranslationCtx, out: &Option<String>) -> PathBuf {
    out.as_ref().map(|s| s.clone().into()).unwrap_or_else(|| {
        let outputs = ctx.tcx.output_filenames(());

        let crate_name = ctx.tcx.crate_name(LOCAL_CRATE);
        let libname = format!("{}{}", crate_name.as_str(), ctx.sess.opts.cg.extra_filename);

        outputs.out_directory.join(&format!("lib{}.cmeta", libname))
    })
}

pub fn dump_exports(ctx: &TranslationCtx, out: &Option<String>) {
    let out_filename = export_file(ctx, out);
    debug!("dump_exports={:?}", out_filename);

    dump_binary_metadata(ctx.tcx, &out_filename, ctx.metadata()).unwrap();
}

fn dump_binary_metadata(
    tcx: TyCtxt<'tcx>,
    path: &Path,
    dep_info: BinaryMetadata<'tcx>,
) -> Result<(), std::io::Error> {
    let mut encoder = MetadataEncoder::new(tcx);
    dep_info.encode(&mut encoder).unwrap();

    File::create(path).and_then(|mut file| file.write(&encoder.into_inner())).map_err(|err| {
        warn!("could not encode metadata for crate `{:?}`, error: {:?}", "LOCAL_CRATE", err);
        err
    })?;
    Ok(())
}

fn load_binary_metadata(
    tcx: TyCtxt<'tcx>,
    cstore: &CStore,
    cnum: CrateNum,
    path: &Path,
) -> Option<BinaryMetadata<'tcx>> {
    let metadata = MetadataBlob::from_file(&path).and_then(|blob| {
        let mut decoder = MetadataDecoder::new(tcx, cnum, &blob);
        match BinaryMetadata::decode(&mut decoder) {
            Ok(m) => Ok(m),
            Err(e) => Err(std::io::Error::new(std::io::ErrorKind::Other, e)),
        }
    });

    match metadata {
        Ok(b) => Some(b),
        Err(e) => {
            warn!("could not read metadata for crate `{:?}`: {:?}", cstore.crate_name(cnum), e);
            return None;
        }
    }
}

fn creusot_metadata_base_path(
    cstore: &CStore,
    overrides: &HashMap<String, String>,
    cnum: CrateNum,
) -> PathBuf {
    if let Some(path) = overrides.get(&cstore.crate_name(cnum).to_string()) {
        debug!("loading crate {:?} from override path", cnum);
        path.into()
    } else {
        let cs = cstore.crate_source_untracked(cnum);
        let x = cs.paths().next().unwrap().clone();
        x
    }
}

fn creusot_metadata_binary_path(mut path: PathBuf) -> PathBuf {
    path.set_extension("cmeta");
    path
}

fn external_crates(tcx: TyCtxt<'tcx>) -> Vec<CrateNum> {
    let mut deps = Vec::new();
    for cr in tcx.crates(()) {
        if let Some(extern_crate) = tcx.extern_crate(cr.as_def_id()) {
            if extern_crate.is_direct() {
                deps.push(*cr);
            }
        }
    }
    deps
}
