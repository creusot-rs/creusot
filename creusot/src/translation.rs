mod builtins;
pub mod constant;
pub mod external;
pub mod function;
pub mod interface;
mod logic;
pub mod specification;
pub mod traits;
pub mod ty;

pub use external::translate_extern;
pub use function::translate_function;
pub use function::LocalIdent;
pub use logic::*;

use heck::CamelCase;

use rustc_hir::def_id::LOCAL_CRATE;
use why3::{
    declaration::{Decl, Module, TyDecl, Use},
    Pretty, QName,
};

use std::io::Result;

use crate::ctx::TranslationCtx;
use std::io::Write;
use why3::mlcfg;

pub fn translate(mut ctx: TranslationCtx<'_, '_>) -> Result<()> {
    ctx.load_metadata();

    for def_id in ctx.tcx.body_owners() {
        let def_id = def_id.to_def_id();
        if !crate::util::should_translate(ctx.tcx, def_id) {
            info!("Skipping {:?}", def_id);
            continue;
        }

        info!("Translating body {:?}", def_id);
        ctx.translate_function(def_id);
    }

    for impls in ctx.tcx.all_local_trait_impls(()).values() {
        for impl_id in impls {
            ctx.translate_impl(impl_id.to_def_id());
        }
    }

    if ctx.should_export() {
        external::dump_exports(&ctx, &ctx.opts.metadata_path);
    }

    if ctx.should_compile() {
        use std::fs::File;

        let mut out: Box<dyn Write> = match ctx.opts.output_file {
            Some(ref f) => Box::new(std::io::BufWriter::new(File::create(f)?)),
            None => Box::new(std::io::stdout()),
        };

        print_crate(
            &mut out,
            ctx.tcx.crate_name(LOCAL_CRATE).to_string().to_camel_case(),
            &ctx.types,
            ctx.modules(),
        )?;
    }

    Ok(())
}

pub fn binop_to_binop(op: rustc_middle::mir::BinOp) -> why3::mlcfg::BinOp {
    use rustc_middle::mir;
    use why3::mlcfg::BinOp;
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

fn unop_to_unop(op: rustc_middle::mir::UnOp) -> why3::mlcfg::UnOp {
    match op {
        rustc_middle::mir::UnOp::Not => why3::mlcfg::UnOp::Not,
        rustc_middle::mir::UnOp::Neg => why3::mlcfg::UnOp::Neg,
    }
}

pub fn prelude_imports(type_import: bool) -> Vec<Decl> {
    let mut imports = vec![
        Decl::UseDecl(Use { name: QName::from_string("Ref").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.Int").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.Int32").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.Int64").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.UInt32").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("mach.int.UInt64").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("string.Char").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("floating_point.Single").unwrap() }),
        Decl::UseDecl(Use { name: QName::from_string("floating_point.Double").unwrap() }),
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
    types: &[TyDecl],
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
            .chain(types.iter().flat_map(|ty| [Decl::TyDecl(ty.clone())]))
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
