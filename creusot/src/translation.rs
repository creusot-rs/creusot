pub mod constant;
pub mod external;
pub mod function;
pub mod interface;
mod logic;
pub mod specification;
pub mod traits;
pub mod ty;

use crate::{
    ctx,
    ctx::{load_extern_specs, TypeDeclaration},
    error::CrErr,
    metadata,
    options::OutputFile,
    validate::{validate_impls, validate_traits},
};
use creusot_rustc::hir::{def::DefKind, def_id::LOCAL_CRATE};
use ctx::TranslationCtx;
pub use function::{translate_function, LocalIdent};
use heck::CamelCase;
pub use logic::*;
use std::{error::Error, io::Write};
use why3::{
    declaration::{Decl, Module, Use},
    mlcfg, Print, QName,
};

pub fn before_analysis(ctx: &mut TranslationCtx) -> Result<(), Box<dyn Error>> {
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
pub fn after_analysis(ctx: &mut TranslationCtx) -> Result<(), Box<dyn Error>> {
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
            ctx.translate_impl(impl_id.to_def_id());
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
        let modules = ctx.modules().flat_map(|(id, item)| {
            if ctx.def_path_str(*id).contains(matcher) {
                item.modules()
            } else {
                item.interface()
            }
        });

        let crate_name = ctx.tcx.crate_name(LOCAL_CRATE).to_string().to_camel_case();
        print_crate(&mut out, crate_name, ctx.types.values(), modules)?;
    }
    debug!("after_analysis_dump: {:?}", start.elapsed());

    Ok(())
}

pub fn binop_to_binop(op: creusot_rustc::middle::mir::BinOp) -> why3::exp::BinOp {
    use creusot_rustc::smir::mir;
    use why3::exp::BinOp;
    match op {
        mir::BinOp::Add => BinOp::Add,
        mir::BinOp::Sub => BinOp::Sub,
        mir::BinOp::Mul => BinOp::Mul,
        mir::BinOp::Div => BinOp::Div,
        mir::BinOp::Eq => BinOp::Eq,
        mir::BinOp::Lt => BinOp::Lt,
        mir::BinOp::Le => BinOp::Le,
        mir::BinOp::Gt => BinOp::Gt,
        mir::BinOp::Ge => BinOp::Ge,
        mir::BinOp::Ne => BinOp::Ne,
        mir::BinOp::Rem => BinOp::Mod,
        _ => unimplemented!("unsupported binary operation: {:?}", op),
    }
}

fn unop_to_unop(op: creusot_rustc::middle::mir::UnOp) -> why3::exp::UnOp {
    match op {
        creusot_rustc::middle::mir::UnOp::Not => why3::exp::UnOp::Not,
        creusot_rustc::middle::mir::UnOp::Neg => why3::exp::UnOp::Neg,
    }
}

pub fn prelude_imports(type_import: bool) -> Vec<Decl> {
    let mut imports = vec![
        Decl::UseDecl(Use { name: QName::from_string("Ref").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.Int").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("prelude.Int8").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("prelude.Int16").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.Int32").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.Int64").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("prelude.UInt8").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("prelude.UInt16").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.UInt32").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.UInt64").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("string.Char").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("floating_point.Single").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("floating_point.Double").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("seq.Seq").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("set.Set").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("set.Fset").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("map.Map").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("prelude.Prelude").unwrap() }),
    ];

    if type_import {
        imports.push(Decl::UseDecl(Use { name: QName::from_string("Type").unwrap() }));
    }
    imports
}

fn print_crate<'a, W, I: Iterator<Item = &'a Module>>(
    out: &mut W,
    _name: String,
    types: impl Iterator<Item = &'a TypeDeclaration>,
    functions: I,
) -> std::io::Result<()>
where
    W: Write,
{
    let (alloc, mut pe) = mlcfg::printer::PrintEnv::new();

    let type_mod = Module {
        name: "Type".into(),
        decls: prelude_imports(false)
            .into_iter()
            .chain(types.flat_map(|ty| {
                std::iter::once(Decl::TyDecl(ty.ty_decl.clone())).chain(ty.accessors().cloned())
            }))
            .collect(),
    };

    type_mod.pretty(&alloc, &mut pe).1.render(120, out)?;
    writeln!(out)?;

    for modl in functions {
        modl.pretty(&alloc, &mut pe).1.render(120, out)?;
        writeln!(out)?;
    }

    Ok(())
}
