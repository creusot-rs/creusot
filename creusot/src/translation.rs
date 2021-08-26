mod builtins;
pub mod constant;
pub mod function;
pub mod specification;
pub mod traits;
pub mod ty;

mod r#extern;
mod logic;

pub use function::translate_function;
pub use logic::*;
pub use r#extern::translate_extern;

use heck::CamelCase;

use rustc_hir::def_id::LOCAL_CRATE;

use std::io::Result;

use why3::mlcfg;

pub fn translate(
    mut ctx: TranslationCtx<'_, '_>,
    output: &Option<String>,
) -> Result<()> {
    debug!("translating bodies={:?}", ctx.tcx.body_owners().collect::<Vec<_>>());   
    for def_id in ctx.tcx.body_owners() {
        let def_id = def_id.to_def_id();
        if !crate::util::should_translate(ctx.tcx, def_id) {
            debug!("Skipping {:?}", def_id);
            continue;
        }

        debug!("Translating body {:?}", def_id);
        ctx.translate_function(def_id);
    }

    use std::fs::File;

    let mut out: Box<dyn Write> = match output {
        Some(f) => Box::new(std::io::BufWriter::new(File::create(f)?)),
        None => Box::new(std::io::stdout()),
    };

    print_crate(&mut out, ctx.tcx.crate_name(LOCAL_CRATE).to_string().to_camel_case(), ctx.modules)?;
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

use std::io::Write;

use crate::ctx::TranslationCtx;

// TODO: integrate crate name into the modules
fn print_crate<W>(out: &mut W, _name: String, krate: crate::modules::Modules) -> std::io::Result<()>
where
    W: Write,
{
    let (alloc, mut pe) = mlcfg::printer::PrintEnv::new();

    for modl in krate.into_iter() {
        modl.pretty(&alloc, &mut pe).1.render(120, out)?;
        writeln!(out)?;
    }

    Ok(())
}
