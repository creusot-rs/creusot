pub(crate) mod constant;
pub(crate) mod external;
#[allow(dead_code)]
pub(crate) mod fmir;
pub(crate) mod function;
pub(crate) mod pearlite;
pub(crate) mod projection_vec;
pub(crate) mod specification;
pub(crate) mod traits;

use crate::{
    backend::{TransId, Why3Generator},
    ctx::{self, load_extern_specs},
    error::InternalError,
    metadata,
    options::OutputFile,
    validate::{validate_impls, validate_opacity, validate_traits},
};
use ctx::TranslationCtx;
use heck::ToUpperCamelCase;
use rustc_hir::{def::DefKind, def_id::LOCAL_CRATE};
use rustc_middle::ty::Ty;
use std::{error::Error, io::Write};
use why3::{declaration::Module, mlcfg, Print};

pub(crate) fn before_analysis(ctx: &mut TranslationCtx) -> Result<(), Box<dyn Error>> {
    let start = Instant::now();
    ctx.load_metadata();
    load_extern_specs(ctx).map_err(|_| Box::new(InternalError("Failed to load extern specs")))?;

    for def_id in ctx.tcx.hir().body_owners() {
        ctx.check_purity(def_id);

        let def_id = def_id.to_def_id();
        if crate::util::is_spec(ctx.tcx, def_id)
            || crate::util::is_predicate(ctx.tcx, def_id)
            || crate::util::is_logic(ctx.tcx, def_id)
        {
            let _ = ctx.term(def_id);
            validate_opacity(ctx, def_id);
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

        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string().to_upper_camel_case();
        print_crate(&mut out, crate_name, modules)?;
        drop(out); //flush the buffer before running why3
        run_why3(&why3, file);
    }
    debug!("after_analysis_dump: {:?}", start.elapsed());

    Ok(())
}
use rustc_middle::mir;

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
        mir::BinOp::Lt => {
            if ty.is_floating_point() {
                BinOp::FloatLt
            } else {
                BinOp::Lt
            }
        }
        mir::BinOp::Le => {
            if ty.is_floating_point() {
                BinOp::FloatLe
            } else {
                BinOp::Le
            }
        }
        mir::BinOp::Gt => {
            if ty.is_floating_point() {
                BinOp::FloatGt
            } else {
                BinOp::Gt
            }
        }
        mir::BinOp::Ge => {
            if ty.is_floating_point() {
                BinOp::FloatGe
            } else {
                BinOp::Ge
            }
        }
        mir::BinOp::Ne => BinOp::Ne,
        mir::BinOp::Rem => BinOp::Mod,
        _ => ctx.crash_and_error(
            rustc_span::DUMMY_SP,
            &format!("unsupported binary operation: {:?}", op),
        ),
    }
}

pub(crate) fn unop_to_unop(ty: Ty, op: rustc_middle::mir::UnOp) -> why3::exp::UnOp {
    match op {
        rustc_middle::mir::UnOp::Not => why3::exp::UnOp::Not,
        rustc_middle::mir::UnOp::Neg => {
            if ty.is_floating_point() {
                why3::exp::UnOp::FloatNeg
            } else {
                why3::exp::UnOp::Neg
            }
        }
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
    let alloc = mlcfg::printer::ALLOC;

    writeln!(out)?;

    for modl in functions {
        modl.pretty(&alloc).1.render(120, out)?;
        writeln!(out)?;
    }

    Ok(())
}
