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
use rustc_hir::Item;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;

use std::io::Result;

use why3::mlcfg;

pub fn translate(
    output: &Option<String>,
    sess: &Session,
    tcx: TyCtxt,
) -> Result<()> {
    let hir_map = tcx.hir();

    // Collect the DefIds of all type declarations in this crate
    let mut ty_decls = Vec::new();

    for (_, mod_items) in tcx.hir_crate(()).modules.iter() {
        for item_id in mod_items.items.iter() {
            let item = hir_map.item(*item_id);
            // What about inline type declarations?
            // How do we find those?
            if is_type_decl(item) {
                ty_decls.push((item.def_id.to_def_id(), item.span));
            }
        }
    }

    // Type translation state, including which datatypes have already been translated.
    let mut ty_ctx = crate::ctx::TranslationCtx::new(tcx, sess);

    debug!("translating bodies={:?}", tcx.body_owners().collect::<Vec<_>>());   
    for def_id in tcx.body_owners() {
        let def_id = def_id.to_def_id();
        if !crate::util::should_translate(tcx, def_id) {
            debug!("Skipping {:?}", def_id);
            continue;
        }

        debug!("Translating body {:?}", def_id);
        ty_ctx.translate_function(def_id);
    }

    use std::fs::File;

    let mut out: Box<dyn Write> = match output {
        Some(f) => Box::new(std::io::BufWriter::new(File::create(f)?)),
        None => Box::new(std::io::stdout()),
    };

    print_crate(&mut out, tcx.crate_name(LOCAL_CRATE).to_string().to_camel_case(), ty_ctx.modules)?;
    Ok(())
}

fn is_type_decl(item: &Item) -> bool {
    match item.kind {
        // rustc_hir::ItemKind::TyAlias(_, _) => true,
        rustc_hir::ItemKind::OpaqueTy(_) => unimplemented!(),
        rustc_hir::ItemKind::Enum(_, _) => true,
        rustc_hir::ItemKind::Struct(_, _) => true,
        rustc_hir::ItemKind::Union(_, _) => unimplemented!(),
        _ => false,
    }
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
