pub(crate) mod constant;
pub(crate) mod external;
#[allow(dead_code)]
pub(crate) mod fmir;
#[allow(unused_imports)]
pub(crate) mod function;
#[allow(unused_imports)]
pub(crate) mod interface;
pub(crate) mod pearlite;
pub(crate) mod specification;
pub(crate) mod traits;
pub(crate) mod ty;

use crate::{
    backend::{
        clone_map2::{Dependency, MonoGraph, PriorClones},
        to_why3,
    },
    ctx::{self, load_extern_specs, ItemType},
    error::CrErr,
    metadata,
    options::OutputFile,
    util,
    validate::{validate_impls, validate_traits},
};
use creusot_rustc::hir::def_id::LOCAL_CRATE;
use ctx::TranslationCtx;
pub(crate) use function::LocalIdent;
use heck::ToUpperCamelCase;
use rustc_middle::ty::Ty;
use std::{collections::HashSet, error::Error, fs::File, io::Write};
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
    let mut graph = MonoGraph::new();

    for def_id in ctx.hir().body_owners() {
        // let def_id = ctx.hir().local_def_id(item_id.hir_id()).to_def_id();
        let def_id = def_id.to_def_id();

        if !crate::util::should_translate(ctx.tcx, def_id) {
            info!("Skipping {:?}", def_id);
            continue;
        }

        let item_type = util::item_type(ctx.tcx, def_id);

        if matches!(item_type, ItemType::Unsupported(_)) {
            continue;
        }

        debug!("Translating item {:?}", def_id);
        ctx.translate(def_id);
        graph.add_root(&mut ctx, def_id);
    }

    for impls in ctx.tcx.all_local_trait_impls(()).values() {
        for impl_id in impls {
            ctx.translate(impl_id.to_def_id());
            graph.add_root(&mut ctx, impl_id.to_def_id());
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
        let mut out = output_writer(&ctx)?;

        let matcher = ctx.opts.match_str.clone();
        let matcher: &str = matcher.as_ref().map(|s| &s[..]).unwrap_or("");
        let tcx = ctx.tcx;

        let priors = PriorClones::from_graph(&mut ctx, &graph);
        let mut modules = Vec::new();
        let mut visited = HashSet::new();
        for dep in graph.iter() {
            let Dependency::Item(id, _) = dep else { continue };
            if tcx.def_path_str(id).contains("eq") {
                eprintln!("Translating {dep:?}");
            }
            if !visited.insert(id) {
                continue;
            };
            let output = if tcx.def_path_str(id).contains(matcher) {
                box to_why3(&mut ctx, &priors, id).into_iter()
            } else {
                let Some(item) = ctx.item(id) else { continue };
                let item = item.clone();
                item.interface()
            };

            modules.extend(output);
        }

        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string().to_upper_camel_case();
        print_crate(&mut out, crate_name, modules.into_iter())?;
    }
    debug!("after_analysis_dump: {:?}", start.elapsed());

    Ok(())
}
use creusot_rustc::smir::mir;

fn output_writer(ctx: &TranslationCtx) -> Result<impl Write, Box<dyn Error>> {
    let out: Box<dyn Write> = match ctx.opts.output_file {
        Some(OutputFile::File(ref f)) => Box::new(std::io::BufWriter::new(File::create(f)?)),
        Some(OutputFile::Stdout) => Box::new(std::io::stdout()),
        None => {
            let outputs = ctx.tcx.output_filenames(());
            let crate_name = ctx.tcx.crate_name(LOCAL_CRATE);

            let libname = format!("{}-{}.mlcfg", crate_name.as_str(), ctx.sess.crate_types()[0]);

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
    Ok(out)
}

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

pub(crate) fn unop_to_unop(op: creusot_rustc::middle::mir::UnOp) -> why3::exp::UnOp {
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
