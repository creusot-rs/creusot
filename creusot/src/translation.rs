pub(crate) mod constant;
pub(crate) mod external;
#[allow(dead_code)]
pub(crate) mod fmir;
pub(crate) mod function;
pub(crate) mod pearlite;
pub(crate) mod specification;
pub(crate) mod traits;

use crate::{
    backend::Why3Generator,
    contracts_items::is_no_translate,
    ctx::{TranslationCtx, gather_params_open_inv},
    metadata,
    translated_item::FileModule,
    validate::validate,
};
use creusot_args::options::{Options, Output};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::ty::TyCtxt;
use std::{collections::HashMap, fs::File, io::Write, path::PathBuf, time::Instant};
use why3::{
    Symbol,
    declaration::{Attribute, Decl, Module},
    printer::{render_decls, render_module},
};

pub(crate) fn before_analysis<'tcx>(tcx: TyCtxt<'tcx>) -> HashMap<DefId, DenseBitSet<usize>> {
    let start = Instant::now();
    let params_open_inv = gather_params_open_inv(tcx);
    debug!("before_analysis: {:?}", start.elapsed());
    params_open_inv
}

fn should_translate(tcx: TyCtxt, mut def_id: DefId) -> bool {
    loop {
        if is_no_translate(tcx, def_id) {
            return false;
        }

        if tcx.is_closure_like(def_id) {
            def_id = tcx.parent(def_id);
        } else {
            return true;
        }
    }
}

// TODO: Move the main loop out of `translation.rs`
pub(crate) fn after_analysis<'tcx>(
    tcx: TyCtxt<'tcx>,
    opts: Options,
    params_open_inv: HashMap<DefId, DenseBitSet<usize>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let start = Instant::now();
    let mut ctx = TranslationCtx::new(tcx, opts.clone(), params_open_inv);
    ctx.load_extern_specs();
    ctx.load_erasures();
    validate(&ctx);
    debug!("after_analysis_validate: {:?}", start.elapsed());
    if let Some(err) = tcx.dcx().has_errors_or_delayed_bugs() {
        err.raise_fatal()
    }

    let start = Instant::now();
    let mut why3 = Why3Generator::new(ctx);
    for def_id in why3.hir_body_owners() {
        let def_id = def_id.to_def_id();

        if !should_translate(why3.tcx, def_id) {
            info!("Skipping {:?}", def_id);
            continue;
        }

        if why3.def_kind(def_id) == DefKind::AnonConst {
            continue;
        }

        info!("Translating body {:?}", def_id);
        why3.translate(def_id);
    }

    for impls in why3.all_local_trait_impls(()).values() {
        for impl_id in impls {
            why3.translate(impl_id.to_def_id());
        }
    }
    why3.dcx().abort_if_errors();

    debug!("after_analysis_translate: {:?}", start.elapsed());
    let start = Instant::now();

    if opts.export_metadata {
        let metadata = why3.ctx.metadata();
        metadata::dump_exports(tcx, &opts.extern_paths, metadata);
    }

    if opts.should_output {
        let output_target = opts.output.clone();
        let prefix = opts.prefix.iter().map(|s| Symbol::intern(s)).collect();
        let modules = why3.functions.into_iter().flat_map(|item| item.modules());
        print_crate(output_target, prefix, modules)?;
    }
    debug!("after_analysis_dump: {:?}", start.elapsed());

    Ok(())
}

pub enum OutputHandle {
    Directory(PathBuf, Vec<Symbol>), // One file per Coma module, second component is a prefix for all files
    File(Box<dyn Write>),            // Monolithic output
}

fn module_output(modl: &FileModule, output: &mut OutputHandle) -> std::io::Result<()> {
    match output {
        OutputHandle::Directory(dir, prefix) => {
            let mut path = dir.clone();
            path.push(modl.path.file_name(&*prefix));
            path.set_extension("coma");
            let prefix = path.parent().unwrap();
            std::fs::create_dir_all(prefix).unwrap();
            modular_output(modl, &mut std::io::BufWriter::new(File::create(path).unwrap()))
        }
        OutputHandle::File(w) => monolithic_output(modl, &mut *w),
    }
}

fn show_attribute(attr: &Attribute) -> String {
    match attr {
        Attribute::Attr(contents) => format!("@{}", contents),
        Attribute::NamedSpan(_name) => panic!("unexpected toplevel named span"),
        Attribute::Span(file, sline, scol, eline, ecol) => {
            format!("#\"{}\" {} {} {} {}", file, sline, scol, eline, ecol)
        }
    }
}

fn modular_output<T: Write>(modl: &FileModule, out: &mut T) -> std::io::Result<()> {
    let FileModule { path: _, modl: Module { name: _, decls, attrs, meta } } = modl;
    let attrs = attrs.iter().map(|attr| Decl::Comment(show_attribute(attr)));
    let meta = meta.iter().map(|s| Decl::Comment(s.clone()));
    let decls: Vec<Decl> = attrs.chain(meta).chain(decls.iter().cloned()).collect();
    render_decls(&decls, out)?;
    writeln!(out)?;
    Ok(())
}

fn monolithic_output<T: Write>(modl: &FileModule, out: &mut T) -> std::io::Result<()> {
    render_module(&modl.modl, out)?;
    writeln!(out)?;
    Ok(())
}

// Remove coma files in the `verif/{krate}/` directory to avoid obsolete files left after
// (re)moving functions in source code.
// We don't want to just `remove_dir_all()` because it may contain
// `proof.json`, `why3session.xml`, and `why3shapes.xml` files that users want to preserve.
fn remove_coma_files(dir: &PathBuf) -> std::io::Result<()> {
    if dir.exists() {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                remove_coma_files(&path)?;
                let _ = std::fs::remove_dir(path); // remove the directory if it's empty, do nothing otherwise
            } else if path.extension().is_some_and(|ext| ext == "coma") {
                std::fs::remove_file(&path)?;
            }
        }
    }
    Ok(())
}

fn print_crate<I: Iterator<Item = FileModule>>(
    output_target: Output,
    prefix: Vec<Symbol>,
    modules: I,
) -> std::io::Result<Option<PathBuf>> {
    let (root, mut output) = match output_target {
        Output::Directory(dir) => {
            let mut outdir = dir.clone();
            for m in &prefix {
                outdir.push(m.to_string());
            }
            remove_coma_files(&outdir)?;
            (Some(dir.clone()), OutputHandle::Directory(dir, prefix))
        }
        Output::File(ref f) => {
            std::fs::create_dir_all(f.parent().unwrap()).unwrap();
            (
                Some(f.clone()),
                OutputHandle::File(Box::new(std::io::BufWriter::new(File::create(f)?))),
            )
        }
        Output::Stdout => (None, OutputHandle::File(Box::new(std::io::stdout()))),
        Output::None => return Ok(None),
    };

    for modl in modules {
        module_output(&modl, &mut output)?;
    }

    //flush the buffer before running why3
    drop(output);

    Ok(root)
}
