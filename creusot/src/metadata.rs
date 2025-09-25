use crate::{
    ctx::*,
    translation::{external::ExternSpec, pearlite::ScopedTerm},
};
use creusot_metadata::{decode_metadata, encode_metadata};
use indexmap::IndexMap;
use once_map::unsync::OnceMap;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::OutputType;
use rustc_span::Symbol;
use std::{
    collections::HashMap,
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
        let mut it = self.crates.iter().filter_map(|cmeta| cmeta.1.creusot_item(sym));
        let r = it.next()?;
        assert!(it.next().is_none());
        return Some(r);
    }

    pub(crate) fn intrinsic(&self, sym: Symbol) -> Option<DefId> {
        let mut it = self.crates.iter().filter_map(|cmeta| cmeta.1.intrinsic(sym));
        let r = it.next()?;
        assert!(it.next().is_none());
        return Some(r);
    }

    pub(crate) fn extern_spec(&self, id: DefId) -> Option<&ExternSpec<'tcx>> {
        self.extern_specs.get(&id)
    }

    pub(crate) fn load(&mut self, tcx: TyCtxt<'tcx>, overrides: &HashMap<String, String>) {
        for &cnum in tcx.crates(()) {
            if cnum == LOCAL_CRATE {
                continue;
            }
            let Some((cmeta, mut ext_specs)) = CrateMetadata::load(tcx, overrides, cnum) else {
                continue;
            };
            self.crates.insert(cnum, cmeta);

            for (id, spec) in ext_specs.drain() {
                if self.extern_specs.insert(id, spec).is_some() {
                    panic!("duplicate external spec found for {:?} while loading {:?}", id, cnum);
                }
            }
        }
    }
}

pub struct CrateMetadata<'tcx> {
    terms: IndexMap<DefId, ScopedTerm<'tcx>>,
    creusot_items: HashMap<Symbol, DefId>,
    intrinsics: HashMap<Symbol, DefId>,
    params_open_inv: HashMap<DefId, Vec<usize>>,
}

impl<'tcx> CrateMetadata<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            terms: Default::default(),
            creusot_items: Default::default(),
            intrinsics: Default::default(),
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

    pub(crate) fn intrinsic(&self, sym: Symbol) -> Option<DefId> {
        self.intrinsics.get(&sym).cloned()
    }

    fn load(
        tcx: TyCtxt<'tcx>,
        overrides: &HashMap<String, String>,
        cnum: CrateNum,
    ) -> Option<(Self, ExternSpecs<'tcx>)> {
        let base_path = creusot_metadata_base_path(tcx, overrides, cnum);

        let binary_path = creusot_metadata_binary_path(base_path.clone());

        let metadata = load_binary_metadata(tcx, cnum, &binary_path)?;

        let mut meta = CrateMetadata::new();

        for (def_id, summary) in metadata.terms.into_iter() {
            meta.terms.insert(def_id, summary);
        }

        meta.intrinsics = metadata.intrinsics;
        meta.creusot_items = metadata.creusot_items;
        meta.params_open_inv = metadata.params_open_inv;

        Some((meta, metadata.extern_specs))
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
    intrinsics: HashMap<Symbol, DefId>,
    extern_specs: HashMap<DefId, ExternSpec<'tcx>>,
    params_open_inv: HashMap<DefId, Vec<usize>>,
}

impl<'tcx> BinaryMetadata<'tcx> {
    pub(crate) fn from_parts(
        terms: &mut OnceMap<DefId, Box<Option<ScopedTerm<'tcx>>>>,
        creusot_items: &HashMap<Symbol, DefId>,
        intrinsics: &HashMap<Symbol, DefId>,
        extern_specs: &HashMap<DefId, ExternSpec<'tcx>>,
        params_open_inv: &HashMap<DefId, Vec<usize>>,
    ) -> Self {
        let terms = terms
            .iter_mut()
            .filter(|(def_id, t)| def_id.is_local() && t.is_some())
            .map(|(id, t)| (*id, t.clone().unwrap()))
            .collect();

        BinaryMetadata {
            terms,
            creusot_items: creusot_items.clone(),
            intrinsics: intrinsics.clone(),
            extern_specs: extern_specs.clone(),
            params_open_inv: params_open_inv.clone(),
        }
    }
}

fn export_file(ctx: &TranslationCtx, out: &Option<String>) -> PathBuf {
    out.as_ref().map(|s| s.clone().into()).unwrap_or_else(|| {
        let outputs = ctx.output_filenames(());
        let out = outputs.path(OutputType::Metadata);
        out.as_path().to_owned().with_extension("cmeta")
    })
}

pub(crate) fn dump_exports(ctx: &mut TranslationCtx) {
    let out_filename = export_file(ctx, &ctx.opts.metadata_path);
    debug!("dump_exports={:?}", out_filename);

    dump_binary_metadata(ctx.tcx, &out_filename, ctx.metadata()).unwrap_or_else(|err| {
        panic!("could not save metadata path=`{:?}` error={}", out_filename, err.1)
    });
}

fn dump_binary_metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    path: &Path,
    dep_info: BinaryMetadata<'tcx>,
) -> Result<(), (PathBuf, std::io::Error)> {
    encode_metadata(tcx, path, dep_info)
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

fn creusot_metadata_base_path(
    tcx: TyCtxt,
    overrides: &HashMap<String, String>,
    cnum: CrateNum,
) -> PathBuf {
    if let Some(path) = overrides.get(&tcx.crate_name(cnum).to_string()) {
        debug!("loading crate {:?} from override path", cnum);
        path.into()
    } else {
        let cs = tcx.used_crate_source(cnum);
        let x = cs.paths().next().unwrap().clone();
        x
    }
}

fn creusot_metadata_binary_path(mut path: PathBuf) -> PathBuf {
    path.set_extension("cmeta");
    path
}
