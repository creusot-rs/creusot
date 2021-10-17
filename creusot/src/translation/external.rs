use crate::function::all_generic_decls_for;
use crate::util::item_type;
use crate::{ctx::*, util};
use creusot_metadata::decoder::{Decodable, MetadataBlob, MetadataDecoder};
use creusot_metadata::encoder::{Encodable, MetadataEncoder};
use indexmap::IndexMap;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_metadata::creader::CStore;
use rustc_middle::middle::cstore::CrateStore;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use why3::declaration::ValKind;
use why3::declaration::{Decl, Module, ValKind::Val};

use super::specification::typing::Term;
use super::{translate_logic, translate_predicate};

pub fn default_decl(ctx: &mut TranslationCtx, def_id: DefId) -> Module {
    info!("generating default declaration for def_id={:?}", def_id);
    let mut names =
        CloneMap::new(ctx.tcx, def_id, util::item_type(ctx.tcx, def_id).is_transparent());

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));

    let sig = crate::util::signature_of(ctx, &mut names, def_id);
    let name = translate_value_id(ctx.tcx, def_id).module_ident().unwrap().clone();

    decls.extend(names.to_clones(ctx));
    let decl = match item_type(ctx.tcx, def_id) {
        ItemType::Logic => ValKind::Function { sig },
        ItemType::Predicate => ValKind::Predicate { sig },
        ItemType::Program => Val { sig },
        _ => unreachable!("default_decl: Expected function"),
    };
    decls.push(Decl::ValDecl(decl));

    Module { name, decls }
}

pub fn extern_module(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (Module, Result<CloneSummary<'tcx>, DefId>) {
    match ctx.externs.terms.get(&def_id) {
        Some(_) => {
            let span = ctx.tcx.def_span(def_id);
            match item_type(ctx.tcx, def_id) {
                // the dependencies should be what was already stored in the metadata...
                ItemType::Logic => (translate_logic(ctx, def_id, span).0, Err(def_id)),
                ItemType::Predicate => (translate_predicate(ctx, def_id, span).0, Err(def_id)),

                _ => unreachable!("extern_module: unexpected term for {:?}", def_id),
            }
        }
        None => {
            let modl = default_decl(ctx, def_id);
            let deps = if ctx.externs.dependencies(def_id).is_some() {
                Err(def_id)
            } else {
                Ok(CloneSummary::new())
            };
            (modl, deps)
        }
    }
}

type CloneMetadata<'tcx> = HashMap<DefId, CloneSummary<'tcx>>;

// TODO: this should lazily load the metadata.
pub struct CrateMetadata<'tcx> {
    tcx: TyCtxt<'tcx>,

    modules: IndexMap<DefId, Module>,
    terms: IndexMap<DefId, Term<'tcx>>,
    dependencies: CloneMetadata<'tcx>,
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
}

use rustc_middle::ty::Visibility;

impl BinaryMetadata<'tcx> {
    pub fn from_parts(
        tcx: TyCtxt<'tcx>,
        functions: &IndexMap<DefId, TranslatedItem<'tcx>>,
        terms: &IndexMap<DefId, Term<'tcx>>,
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

        BinaryMetadata { dependencies, terms }
    }
}

impl CrateMetadata<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            modules: Default::default(),
            dependencies: Default::default(),
            terms: Default::default(),
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

    pub fn load(&mut self, overrides: &HashMap<String, String>) {
        let cstore = CStore::from_tcx(self.tcx);
        for cnum in external_crates(self.tcx) {
            self.load_crate(cstore, overrides, cnum);
        }
    }

    fn load_crate(&mut self, cstore: &CStore, overrides: &HashMap<String, String>, cnum: CrateNum) {
        let base_path = creusot_metadata_base_path(cstore, overrides, cnum);

        let binary_path = creusot_metadata_binary_path(base_path.clone());

        if let Some(metadata) = load_binary_metadata(self.tcx, cstore, cnum, &binary_path) {
            for (def_id, summary) in metadata.dependencies.into_iter() {
                self.dependencies.insert(def_id, summary.into_iter().collect());
            }

            for (def_id, summary) in metadata.terms.into_iter() {
                self.terms.insert(def_id, summary);
            }
        }
    }
}

fn export_file(ctx: &TranslationCtx, out: &Option<String>) -> PathBuf {
    out.as_ref().map(|s| s.clone().into()).unwrap_or_else(|| {
        let outputs = ctx.tcx.output_filenames(());

        let crate_name = ctx.tcx.crate_name(LOCAL_CRATE).as_str();
        let libname = format!("{}{}", crate_name, ctx.sess.opts.cg.extra_filename);

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
