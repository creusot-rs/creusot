mod builtins;
pub mod constant;
pub mod function;
pub mod specification;
pub mod traits;
pub mod ty;

pub mod external;
mod logic;

pub use external::translate_extern;
pub use function::translate_function;
pub use logic::*;
pub use function::LocalIdent;

use heck::CamelCase;

use rustc_hir::def_id::LOCAL_CRATE;
use why3::{Pretty,
    declaration::{Decl, Module, TyDecl, Use},
    QName,
};

use std::io::Result;

use crate::ctx::TranslationCtx;
use why3::mlcfg;

pub fn translate(mut ctx: TranslationCtx<'_, '_>) -> Result<()> {
    load_exports(&mut ctx);

    for def_id in ctx.tcx.body_owners() {
        let def_id = def_id.to_def_id();
        if !crate::util::should_translate(ctx.tcx, def_id) {
            info!("Skipping {:?}", def_id);
            continue;
        }

        info!("Translating body {:?}", def_id);
        ctx.translate_function(def_id);
    }

    for (_, impls) in ctx.tcx.all_local_trait_impls(()) {
        for impl_id in impls {
            traits::translate_impl(&mut ctx, impl_id.to_def_id());
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
            ctx.types,
            ctx.functions.values(),
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
        _ => unimplemented!("unsupported binary operation: {:?}", op),
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

use std::io::Write;

use self::external::load_exports;

fn print_crate<'a, W, I: Iterator<Item = &'a Module>>(
    out: &mut W,
    _name: String,
    types: Vec<TyDecl>,
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
            .chain(types.into_iter().flat_map(|ty| [Decl::TyDecl(ty)]))
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
