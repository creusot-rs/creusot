pub(crate) mod constant;
pub(crate) mod external;
#[allow(dead_code)]
pub(crate) mod fmir;
pub(crate) mod function;
pub(crate) mod pearlite;
mod projection_vec;
pub(crate) mod specification;
pub(crate) mod traits;
use std::{fs::File, path::PathBuf};

use crate::{
    backend::{TransId, Why3Generator},
    ctx::{self, load_extern_specs},
    error::InternalError,
    metadata,
    options::Output,
    special_items::attributes,
    translated_item::FileModule,
    validate::{
        validate_impls, validate_opacity, validate_purity, validate_traits, validate_trusted,
    },
};
use ::why3::{
    declaration::{Decl, Module},
    mlcfg, Print,
};
use ctx::TranslationCtx;
use rustc_hir::def::DefKind;
use rustc_span::{Symbol, DUMMY_SP};
use std::{error::Error, io::Write};
use why3::{declaration::Attribute, mlcfg::printer::pretty_blocks};

pub(crate) fn before_analysis(ctx: &mut TranslationCtx) -> Result<(), Box<dyn Error>> {
    let start = Instant::now();

    if ctx.get_diagnostic_item(Symbol::intern("creusot_resolve")) == None {
        ctx.fatal_error(DUMMY_SP, "The `creusot_contracts` crate is not loaded. You will not be able to verify any code using Creusot until you do so.").emit();
    }

    ctx.load_metadata();
    load_extern_specs(ctx).map_err(|_| Box::new(InternalError("Failed to load extern specs")))?;

    for def_id in ctx.tcx.hir().body_owners() {
        validate_purity(ctx, def_id);

        let def_id = def_id.to_def_id();
        if attributes::is_spec(ctx.tcx, def_id)
            || attributes::is_predicate(ctx.tcx, def_id)
            || attributes::is_logic(ctx.tcx, def_id)
        {
            let _ = ctx.term(def_id);
            validate_opacity(ctx, def_id);
        }
    }
    crate::validate_terminates::validate_terminates(ctx);

    // Check that all trait laws are well-formed
    validate_traits(ctx);
    validate_impls(ctx);
    validate_trusted(ctx);

    debug!("before_analysis: {:?}", start.elapsed());
    Ok(())
}

use std::time::Instant;
// TODO: Move the main loop out of `translation.rs`
pub(crate) fn after_analysis(ctx: TranslationCtx) -> Result<(), Box<dyn Error>> {
    let mut why3 = Why3Generator::new(ctx);

    let start = Instant::now();
    for def_id in why3.hir().body_owners() {
        let def_id = def_id.to_def_id();

        if !crate::util::should_translate(why3.tcx, def_id) {
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

    debug!("after_analysis_translate: {:?}", start.elapsed());
    let start = Instant::now();

    if why3.dcx().has_errors().is_some() {
        return Err(Box::new(InternalError("Failed to generate correct why3")));
    }

    if why3.should_export() {
        metadata::dump_exports(&why3, &why3.opts.metadata_path);
    }

    if why3.should_compile() {
        use crate::run_why3::run_why3;

        let matcher = why3.opts.match_str.clone();
        let matcher: &str = matcher.as_ref().map(|s| &s[..]).unwrap_or("");
        let tcx = why3.tcx;
        let output_target = why3.opts.output.clone();
        let modules = why3.modules();
        let modules = modules.flat_map(|(id, item)| {
            if let TransId::Item(did) = id
                && tcx.def_path_str(did).contains(matcher)
            {
                item.modules()
            } else {
                Box::new(std::iter::empty())
            }
        });

        let file = print_crate(output_target, modules)?;
        run_why3(&why3, file);
    }
    debug!("after_analysis_dump: {:?}", start.elapsed());

    Ok(())
}

pub enum OutputHandle {
    Directory(PathBuf),   // One file per Coma module
    File(Box<dyn Write>), // Monolithic output
}

fn module_output(modl: &FileModule, output: &mut OutputHandle) -> std::io::Result<()> {
    match output {
        OutputHandle::Directory(dir) => {
            let mut path = dir.clone();
            path.push(modl.path.file_name());
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
        Attribute::NamedSpan(name) => format!("%#{}", name),
        Attribute::Span(file, sline, scol, eline, ecol) => {
            format!("#\"{}\" {} {} {} {}", file, sline, scol, eline, ecol)
        }
    }
}

fn modular_output<T: Write>(modl: &FileModule, out: &mut T) -> std::io::Result<()> {
    let FileModule { path: _, modl: Module { name: _, decls, attrs, meta } } = modl;
    let attrs = attrs.into_iter().map(|attr| Decl::Comment(show_attribute(attr)));
    let meta = meta.into_iter().map(|s| Decl::Comment(s.clone()));
    let decls: Vec<Decl> = attrs.chain(meta).chain(decls.into_iter().cloned()).collect();
    pretty_blocks(&decls, &mlcfg::printer::ALLOC).1.render(120, out)?;
    writeln!(out)?;
    Ok(())
}

fn monolithic_output<T: Write>(modl: &FileModule, out: &mut T) -> std::io::Result<()> {
    modl.modl.pretty(&mlcfg::printer::ALLOC).1.render(120, out)?;
    writeln!(out)?;
    Ok(())
}

fn print_crate<I: Iterator<Item = FileModule>>(
    output_target: Output,
    modules: I,
) -> std::io::Result<Option<PathBuf>> {
    let (root, mut output) = match output_target {
        Output::Directory(dir) => (Some(dir.clone()), OutputHandle::Directory(dir)),
        Output::File(ref f) => {
            std::fs::create_dir_all(f.parent().unwrap()).unwrap();
            (
                Some(f.clone()),
                OutputHandle::File(Box::new(std::io::BufWriter::new(File::create(f)?))),
            )
        }
        Output::Stdout => (None, OutputHandle::File(Box::new(std::io::stdout()))),
    };

    for modl in modules {
        module_output(&modl, &mut output)?;
    }

    //flush the buffer before running why3
    drop(output);

    Ok(root)
}
