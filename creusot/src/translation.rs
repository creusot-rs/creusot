pub(crate) mod constant;
pub(crate) mod external;
#[allow(dead_code)]
pub(crate) mod fmir;
pub(crate) mod function;
pub(crate) mod pearlite;
mod projection_vec;
pub(crate) mod specification;
pub(crate) mod traits;

use crate::{
    attributes::{is_logic, is_predicate, is_spec, should_translate},
    backend::{TransId, Why3Generator},
    ctx,
    error::InternalError,
    metadata,
    naming::translate_name,
    options::OutputFile,
    validate::{
        validate_impls, validate_opacity, validate_purity, validate_traits, validate_trusted,
    },
};
use ctx::TranslationCtx;
use rustc_hir::{def::DefKind, def_id::LOCAL_CRATE};
use rustc_span::{Symbol, DUMMY_SP};
use std::{error::Error, io::Write};
use why3::{declaration::Module, mlcfg, Print};

pub(crate) fn before_analysis(ctx: &mut TranslationCtx) -> Result<(), Box<dyn Error>> {
    let start = Instant::now();

    if ctx.get_diagnostic_item(Symbol::intern("creusot_resolve")) == None {
        ctx.fatal_error(DUMMY_SP, "The `creusot_contracts` crate is not loaded. You will not be able to verify any code using Creusot until you do so.").emit();
    }

    ctx.load_metadata();
    ctx.load_extern_specs().map_err(|_| Box::new(InternalError("Failed to load extern specs")))?;

    for def_id in ctx.tcx.hir().body_owners() {
        validate_purity(ctx, def_id);

        let def_id = def_id.to_def_id();
        if is_spec(ctx.tcx, def_id) || is_predicate(ctx.tcx, def_id) || is_logic(ctx.tcx, def_id) {
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
        use std::fs::File;
        let file = match why3.opts.output_file {
            OutputFile::File(ref f) => Some(f.clone().into()),
            OutputFile::Stdout => None,
        };
        let mut out: Box<dyn Write> = match &file {
            Some(f) => Box::new(std::io::BufWriter::new(File::create(f)?)),
            None => Box::new(std::io::stdout()),
        };

        let matcher = why3.opts.match_str.clone();
        let matcher: &str = matcher.as_ref().map(|s| &s[..]).unwrap_or("");
        let tcx = why3.tcx;
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

        let crate_name = translate_name(&tcx.crate_name(LOCAL_CRATE).to_string());
        print_crate(&mut out, crate_name, modules)?;
        drop(out); //flush the buffer before running why3
        run_why3(&why3, file);
    }
    debug!("after_analysis_dump: {:?}", start.elapsed());

    Ok(())
}

fn print_crate<W, I: Iterator<Item = Module>>(
    out: &mut W,
    _name: String,
    functions: I,
) -> std::io::Result<()>
where
    W: Write,
{
    let alloc = mlcfg::printer::ALLOC;

    writeln!(out)?;

    for modl in functions {
        modl.pretty(&alloc).1.render(120, out)?;
        writeln!(out)?;
    }

    Ok(())
}
