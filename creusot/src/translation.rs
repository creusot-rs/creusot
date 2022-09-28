pub(crate) mod constant;
pub(crate) mod external;
#[allow(dead_code)]
pub(crate) mod fmir;
pub(crate) mod function;
pub(crate) mod interface;
mod logic;
pub(crate) mod specification;
pub(crate) mod traits;
pub(crate) mod ty;

use crate::{
    ctx,
    ctx::load_extern_specs,
    error::CrErr,
    metadata,
    options::OutputFile,
    validate::{validate_impls, validate_traits},
};
use creusot_rustc::hir::{def::DefKind, def_id::LOCAL_CRATE};
use ctx::TranslationCtx;
pub(crate) use function::{translate_function, LocalIdent};
use heck::CamelCase;
pub(crate) use logic::*;
use rustc_middle::ty::Ty;
use std::{error::Error, io::Write};
use why3::{declaration::Module, mlcfg, Print};

pub(crate) fn before_analysis(ctx: &mut TranslationCtx) -> Result<(), Box<dyn Error>> {
    let start = Instant::now();
    ctx.load_metadata();
    load_extern_specs(ctx).map_err(|_| Box::new(CrErr))?;

    for def_id in ctx.tcx.hir().body_owners() {
        let def_id = def_id.to_def_id();
        if crate::util::is_spec(ctx.tcx, def_id)
            || crate::util::is_logic(ctx.tcx, def_id)
            || crate::util::is_predicate(ctx.tcx, def_id)
        {
            let _ = ctx.term(def_id);
        }
    }

    // Check that all trait laws are well-formed
    validate_traits(ctx);
    validate_impls(ctx);

    debug!("before_analysis: {:?}", start.elapsed());
    Ok(())
}

use std::time::Instant;
// TODO: Move the main loop out of `translation.rs`
pub(crate) fn after_analysis(mut ctx: TranslationCtx) -> Result<(), Box<dyn Error>> {
    for tr in ctx.tcx.traits_in_crate(LOCAL_CRATE) {
        ctx.translate_trait(*tr);
    }

    let start = Instant::now();
    for def_id in ctx.tcx.hir().body_owners() {
        let def_id = def_id.to_def_id();

        if !crate::util::should_translate(ctx.tcx, def_id) {
            info!("Skipping {:?}", def_id);
            continue;
        }

        if ctx.def_kind(def_id) == DefKind::AnonConst {
            continue;
        }

        info!("Translating body {:?}", def_id);
        ctx.translate(def_id);
    }

    for impls in ctx.tcx.all_local_trait_impls(()).values() {
        for impl_id in impls {
            ctx.translate(impl_id.to_def_id());
        }
    }

    debug!("after_analysis_translate: {:?}", start.elapsed());
    let start = Instant::now();

    if ctx.tcx.sess.has_errors().is_some() {
        return Err(Box::new(CrErr));
    }

    if ctx.should_export() {
        metadata::dump_exports(&ctx, &ctx.opts.metadata_path);
    }

    if ctx.should_compile() {
        use std::fs::File;
        let mut out: Box<dyn Write> = match ctx.opts.output_file {
            Some(OutputFile::File(ref f)) => Box::new(std::io::BufWriter::new(File::create(f)?)),
            Some(OutputFile::Stdout) => Box::new(std::io::stdout()),
            None => {
                let outputs = ctx.tcx.output_filenames(());
                let crate_name = ctx.tcx.crate_name(LOCAL_CRATE);

                let libname =
                    format!("{}-{}.mlcfg", crate_name.as_str(), ctx.sess.crate_types()[0]);

                let directory = if ctx.opts.in_cargo {
                    let mut dir = outputs.out_directory.clone();
                    dir.pop();
                    dir
                } else {
                    outputs.out_directory.clone()
                };
                let out_path = directory.join(&libname);
                Box::new(std::io::BufWriter::new(File::create(out_path)?))
            }
        };

        let matcher: &str = ctx.opts.match_str.as_ref().map(|s| &s[..]).unwrap_or("");
        let tcx = ctx.tcx;
        let modules = ctx.modules().flat_map(|(id, item)| {
            if tcx.def_path_str(id).contains(matcher) {
                item.modules()
            } else {
                item.interface()
            }
        });

        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string().to_camel_case();
        print_crate(&mut out, crate_name, modules)?;
    }
    debug!("after_analysis_dump: {:?}", start.elapsed());

    Ok(())
}
use creusot_rustc::smir::mir;

pub(crate) fn binop_to_binop(ctx: &mut TranslationCtx, ty: Ty, op: mir::BinOp) -> why3::exp::BinOp {
    use why3::exp::BinOp;
    match op {
        mir::BinOp::Add => {
            if ty.is_floating_point() {
                BinOp::FloatAdd
            } else {
                BinOp::Add
            }
        }
        mir::BinOp::Sub => {
            if ty.is_floating_point() {
                BinOp::FloatSub
            } else {
                BinOp::Sub
            }
        }
        mir::BinOp::Mul => {
            if ty.is_floating_point() {
                BinOp::FloatMul
            } else {
                BinOp::Mul
            }
        }
        mir::BinOp::Div => {
            if ty.is_floating_point() {
                BinOp::FloatDiv
            } else {
                BinOp::Div
            }
        }
        mir::BinOp::Eq => {
            if ty.is_floating_point() {
                BinOp::FloatEq
            } else {
                BinOp::Eq
            }
        }
        mir::BinOp::Lt => BinOp::Lt,
        mir::BinOp::Le => BinOp::Le,
        mir::BinOp::Gt => BinOp::Gt,
        mir::BinOp::Ge => BinOp::Ge,
        mir::BinOp::Ne => BinOp::Ne,
        mir::BinOp::Rem => BinOp::Mod,
        _ => ctx.crash_and_error(
            creusot_rustc::span::DUMMY_SP,
            &format!("unsupported binary operation: {:?}", op),
        ),
    }
}

fn unop_to_unop(op: creusot_rustc::middle::mir::UnOp) -> why3::exp::UnOp {
    match op {
        creusot_rustc::middle::mir::UnOp::Not => why3::exp::UnOp::Not,
        creusot_rustc::middle::mir::UnOp::Neg => why3::exp::UnOp::Neg,
    }
}

fn print_crate<W, I: Iterator<Item = Module>>(
    out: &mut W,
    _name: String,
    functions: I,
) -> std::io::Result<()>
where
    W: Write,
{
    let (alloc, mut pe) = mlcfg::printer::PrintEnv::new();

    writeln!(out)?;

    for modl in functions {
        modl.pretty(&alloc, &mut pe).1.render(120, out)?;
        writeln!(out)?;
    }

    Ok(())
}
