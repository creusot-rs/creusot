use crate::function::all_generic_decls_for;
use crate::{ctx::*, util};
use creusot_metadata::decoder::{Decodable, MetadataBlob, MetadataDecoder};
use creusot_metadata::encoder::{Encodable, MetadataEncoder};
use indexmap::IndexMap;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_index::vec::Idx;
use rustc_metadata::creader::CStore;
use rustc_middle::middle::cstore::CrateStore;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::{TyCtxt, Visibility};
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use why3::declaration::{Decl, Module, ValKind::Val};

// Translate functions that are external to the crate as opaque values
pub fn translate_extern(ctx: &mut TranslationCtx, def_id: DefId, span: rustc_span::Span) -> Module {
    debug!("using external info for def_id={:?}", def_id);
    match ctx.externs.body(def_id) {
        Some(modl) => modl.clone(),
        None => default_decl(ctx, def_id, span),
    }
}

fn default_decl(ctx: &mut TranslationCtx, def_id: DefId, _span: rustc_span::Span) -> Module {
    debug!("generating default declaration for def_id={:?}", def_id);
    let mut names = CloneMap::new(ctx.tcx, util::item_type(ctx.tcx, def_id));

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));

    let sig = crate::util::signature_of(ctx, &mut names, def_id);
    let name = translate_value_id(ctx.tcx, def_id).module_name().unwrap().clone();

    decls.extend(names.to_clones(ctx));
    decls.push(Decl::ValDecl(Val { sig }));

    Module { name, decls }
}

type CloneMetadata<'tcx> = HashMap<DefId, CloneSummary<'tcx>>;

// TODO: this should lazily load the metadata.
pub struct CrateMetadata<'tcx> {
    tcx: TyCtxt<'tcx>,

    modules: IndexMap<DefId, Module>,
    dependencies: CloneMetadata<'tcx>,
}

impl CrateMetadata<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx, modules: Default::default(), dependencies: Default::default() }
    }

    pub fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        assert!(!def_id.is_local());
        self.dependencies.get(&def_id)
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

        if let Some(dep_info) = load_binary_metadata(self.tcx, cstore, cnum, &binary_path) {
            for (def_id, summary) in dep_info.into_iter() {
                self.dependencies.insert(def_id, summary.into_iter().collect());
            }
        }

        let binary_path = creusot_metadata_logic_path(base_path);

        if let Some(functions) = load_logic_metadata(cstore, cnum, &binary_path) {
            self.modules.extend(functions)
        }
    }
}

type LogicMetadata<'a> = IndexMap<usize, &'a Module>;
type CloneMetaSerialize<'tcx> = HashMap<DefId, Vec<((DefId, SubstsRef<'tcx>), String)>>;

fn export_file(ctx: &TranslationCtx, out: &Option<String>) -> PathBuf {
    out.as_ref().map(|s| s.clone().into()).unwrap_or_else(|| {
        let outputs = ctx.tcx.output_filenames(());

        let crate_name = ctx.tcx.crate_name(LOCAL_CRATE).as_str();
        let libname = format!("{}{}", crate_name, ctx.sess.opts.cg.extra_filename);

        outputs.out_directory.join(&format!("lib{}.creusot", libname))
    })
}

#[deprecated = "use MetadataDecoder instead"]
pub fn dump_exports(ctx: &TranslationCtx, out: &Option<String>) {
    let mut out_filename = export_file(ctx, out);

    debug!("dump_exports={:?}", out_filename);

    let exports = logic_declaration_metadata(ctx);
    let res = std::fs::File::create(out_filename.clone())
        .and_then(|mut file| serde_json::to_writer(&mut file, &exports).map_err(|e| e.into()));

    if let Err(err) = res {
        warn!("failed to dump creusot metadata err={:?}", err);
    };

    out_filename.set_extension("cmeta");

    let clone_metadata = clone_metadata(ctx);

    dump_binary_metadata(ctx.tcx, &out_filename, clone_metadata).unwrap();
}

fn logic_declaration_metadata<'a>(ctx: &'a TranslationCtx<'_, '_>) -> LogicMetadata<'a> {
    ctx.functions
        .iter()
        .filter(|(def_id, _)| {
            ctx.tcx.visibility(**def_id) == Visibility::Public && def_id.is_local()
        })
        .map(|(def_id, func)| (def_id.expect_local().index(), func.body()))
        .collect()
}

fn clone_metadata(ctx: &TranslationCtx<'_, 'tcx>) -> CloneMetaSerialize<'tcx> {
    ctx.functions
        .iter()
        .filter(|(def_id, _)| {
            ctx.tcx.visibility(**def_id) == Visibility::Public && def_id.is_local()
        })
        .map(|(def_id, v)| (*def_id, v.dependencies().clone().into_iter().collect()))
        .collect()
}

fn dump_binary_metadata(
    tcx: TyCtxt<'tcx>,
    path: &Path,
    dep_info: CloneMetaSerialize<'tcx>,
) -> Result<(), std::io::Error> {
    let mut encoder = MetadataEncoder::new(tcx);
    dep_info.encode(&mut encoder).unwrap();
    // encode_index_map(&dep_info, &mut encoder).unwrap();

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
) -> Option<CloneMetadata<'tcx>> {
    let blob = match MetadataBlob::from_file(&path) {
        Ok(b) => b,
        Err(_) => {
            warn!("could not read dependency metadata for crate `{:?}`", cstore.crate_name(cnum));
            return None;
        }
    };

    let mut decoder = MetadataDecoder::new(tcx, cnum, &blob);
    let map = match CloneMetaSerialize::decode(&mut decoder) {
        Ok(b) => b,
        Err(_) => {
            warn!("could not read dependency metadata for crate `{:?}`", cstore.crate_name(cnum));
            return None;
        }
    };

    Some(map.into_iter().map(|(id, vec)| (id, vec.into_iter().collect())).collect())
    // Some(map)
}

fn load_logic_metadata(
    cstore: &CStore,
    cr: CrateNum,
    path: &Path,
) -> Option<impl Iterator<Item = (DefId, Module)>> {
    let rdr = File::open(path);

    if let Err(err) = rdr {
        warn!("could not load metadata for crate={:?} err={:?}", cstore.crate_name(cr), err);
        return None;
    }
    let map_res: Result<IndexMap<u32, _>, _> = serde_json::from_reader(rdr.unwrap());

    if let Err(err) = map_res {
        warn!("error reading metadata for crate={:?} err={:?}", cr, err);
        return None;
    }

    Some(
        map_res
            .unwrap()
            .into_iter()
            .map(move |(ix, val)| (DefId { krate: cr, index: ix.into() }, val)),
    )
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

fn creusot_metadata_logic_path(mut path: PathBuf) -> PathBuf {
    path.set_extension("creusot");
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
