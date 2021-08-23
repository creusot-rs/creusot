use indexmap::IndexMap;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::ty::Visibility;

use super::logic::*;
use why3::declaration::{Decl, Module, ValKind::Val};

use crate::ctx::*;
use crate::function::all_generic_decls_for;

// Translate functions that are external to the crate as opaque values
pub fn translate_extern(ctx: &mut TranslationCtx, def_id: DefId, span: rustc_span::Span) -> Module {
    debug!("using external info for def_id={:?}", def_id);
    match ctx.externs.get(&def_id) {
        Some(modl) => modl.clone(),
        None => default_decl(ctx, def_id, span),
    }
}

fn default_decl(ctx: &mut TranslationCtx, def_id: DefId, _span: rustc_span::Span) -> Module {
    let mut names = NameMap::new(ctx.tcx);
    let sig = crate::util::signature_of(ctx, &mut names, def_id);

    let name = translate_value_id(ctx.tcx, def_id).module.join("");

    let mut decls : Vec<_> = super::prelude_imports(true);
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));

    decls.push(Decl::ValDecl(Val { sig }));

    Module { name, decls }
}

use rustc_index::vec::Idx;
use rustc_hir::def_id::LOCAL_CRATE;

fn export_file(ctx: &TranslationCtx, out: &Option<String>) -> PathBuf {
    out.as_ref().map(|s| s.clone().into()).unwrap_or_else(|| {
        let outputs = ctx.tcx.output_filenames(());

        let crate_name = ctx.tcx.crate_name(LOCAL_CRATE).as_str();
        let libname = format!("{}{}", crate_name, ctx.sess.opts.cg.extra_filename);

        outputs.out_directory.join(&format!("lib{}.creusot", libname))
    })
}

pub fn dump_exports(ctx: &TranslationCtx, out: &Option<String>) {
    let out_filename = export_file(ctx, out);
    
    debug!("dump_exports={:?}", out_filename);  

    let exports : IndexMap<_, _>= ctx.functions.iter().filter(|(def_id, _)| {
        ctx.tcx.visibility(**def_id) == Visibility::Public && def_id.is_local()
    })
    .map(|(def_id, func)| (def_id.expect_local().index(), func)).collect();

    let res = std::fs::File::create(out_filename).and_then(|mut file| {
        serde_json::to_writer(&mut file, &exports).map_err(|e| e.into())
    });

    if let Err(err) = res {
        warn!("failed to dump creusot metadata err={:?}", err);
    };
}

pub fn load_exports(ctx: &mut TranslationCtx) {
    let cstore = CStore::from_tcx(ctx.tcx);
    for cr in external_crates(&ctx) {
        ctx.externs.extend(load_crate_creusot_metadata(cstore, &ctx.opts.extern_paths, cr))
    }
}

use rustc_metadata::creader::CStore;
use rustc_middle::middle::cstore::CrateStore;
use std::collections::HashMap;
fn load_crate_creusot_metadata(cstore: &CStore, externs: &HashMap<String, String>, cr: CrateNum) -> IndexMap<DefId, Module> {
    let creusot_path = if let Some(path) = externs.get(&cstore.crate_name(cr).to_string()) {
        debug!("loading crate {:?} from extern path", cr);
        path.into()
    } else {
        let cs = cstore.crate_source_untracked(cr);
        crate_creusot_data_path(&cs)
    };

    debug!("loading metadata from path={:?}", creusot_path);

    let rdr = std::fs::File::open(creusot_path);

    if let Err(err) = rdr {
        warn!("could not load metadata for crate={:?} err={:?}", cstore.crate_name(cr), err);
        return IndexMap::new();
    }
    let map_res : Result<IndexMap<u32, _>, _> = serde_json::from_reader(rdr.unwrap());

    if let Err(err) = map_res {
        warn!("error reading metadata for crate={:?} err={:?}", cr, err);
        return IndexMap::new();
    }

    map_res.unwrap().into_iter().map(|(ix, val)| {
        (DefId { krate: cr, index: ix.into() }, val)
    }).collect()

}

use rustc_middle::middle::cstore::CrateSource;
use std::path::{Path, PathBuf};
/// Constructs a path to creusot metadata (if present) using the crate source
/// We store the metadata in a `.creusot` json file alongside the rest of the build artifacts
fn crate_creusot_data_path(src: &CrateSource) -> PathBuf {
    let mut path = src.paths().nth(0).unwrap().clone();
    path.set_extension("creusot");
    path
}

fn external_crates<'tcx>(ctx: &TranslationCtx<'_, 'tcx>) -> Vec<CrateNum> {
    let mut deps = Vec::new();
    for cr in ctx.tcx.crates(()) {
        if let Some(extern_crate) = ctx.tcx.extern_crate(cr.as_def_id()) {
            if extern_crate.is_direct() {
                deps.push(*cr);
            }
        }
    }
    deps
}