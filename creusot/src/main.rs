#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![register_tool(creusot)]
#![feature(const_panic)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
extern crate log;

use heck::CamelCase;
use rustc_driver::{abort_on_err, Callbacks, Compilation, RunCompiler};
use rustc_hir::{def_id::LOCAL_CRATE, Item};
use rustc_interface::{
    interface::{BoxedResolver, Compiler},
    Queries,
};
use rustc_middle::{
    mir::{visit::MutVisitor, Location, Terminator},
    ty::{TyCtxt, WithOptConstParam},
};
use std::{cell::RefCell, env::args as get_args, rc::Rc};
use why3::mlcfg;

mod analysis;
pub mod ctx;
mod extended_location;
mod translation;

#[allow(dead_code)]
mod debug;

use rustc_session::Session;
use translation::*;

mod modules;

struct ToWhy {
    output_file: Option<String>,
}

impl Callbacks for ToWhy {
    fn after_expansion<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        let session = c.session();
        let resolver = {
            let parts = abort_on_err(queries.expansion(), session).peek();
            let resolver = parts.1.borrow();
            resolver.clone()
        };

        queries.prepare_outputs().unwrap();

        queries.global_ctxt().unwrap();

        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| tcx.analysis(LOCAL_CRATE)).unwrap();

        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| {
                let session = c.session();
                // TODO: Resolve extern crates
                translate(&self.output_file, session, tcx, resolver)
            })
            .unwrap();
        Compilation::Stop
    }
}

fn main() {
    env_logger::init();

    let mut args = get_args().collect::<Vec<String>>();

    let output_file = args.iter().position(|a| a == "-o").map(|ix| args[ix + 1].clone());

    args.push(format!("--sysroot={}", sysroot_path()));
    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    // args.push("-Znll-facts".to_owned());
    RunCompiler::new(&args, &mut ToWhy { output_file }).run().unwrap();
}

use std::io::Result;

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

fn translate(
    output: &Option<String>,
    sess: &Session,
    tcx: TyCtxt,
    resolver: Rc<RefCell<BoxedResolver>>,
) -> Result<()> {
    let hir_map = tcx.hir();

    // Collect the DefIds of all type declarations in this crate
    let mut ty_decls = Vec::new();
    log::debug!("translate");

    for (_, mod_items) in tcx.hir_crate(LOCAL_CRATE).modules.iter() {
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
    let mut ty_ctx = ctx::TranslationCtx::new(tcx, sess);

    // Translate all type declarations and push them into the module collection
    for (def_id, span) in ty_decls.iter() {
        debug!("Translating type declaration {:?}", def_id);
        translation::ty::translate_tydecl(&mut ty_ctx, *span, *def_id);
    }

    for def_id in tcx.body_owners() {
        debug!("Translating body {:?}", def_id);
        // (Mir-)Borrowck uses `mir_validated`, so we have to force it to
        // execute before we can steal.
        //
        // We want to capture MIR here for the simple reason that it is before
        // Aggregates are destructured. This means that we don't have to deal with the whole
        // 'assign each field and the discriminant' seperately stuff.

        let _ = tcx.mir_borrowck(def_id);

        let (body, _) = tcx.mir_promoted(WithOptConstParam::unknown(def_id));
        let mut body = body.steal();
        let def_id = def_id.to_def_id();

        // Parent module of declaration
        let module_id = tcx.parent_module_from_def_id(def_id.expect_local()).to_def_id();
        // let module_id = tcx.parent(def_id).unwrap();
        let resolver = specification::RustcResolver(resolver.clone(), module_id, tcx);

        use specification::Spec::*;
        match specification::spec_kind(tcx, def_id).unwrap() {
            Invariant { .. } => continue,
            Logic { body: exp, contract } => {
                let out_contract = contract.check_and_lower(&resolver, &mut ty_ctx, &body);

                let translated = specification::logic_to_why(
                    &resolver,
                    &mut ty_ctx,
                    def_id,
                    &body,
                    exp,
                    out_contract,
                );

                ty_ctx.modules.add_module(translated)
            }
            Program { contract } => {
                let mut out_contract = contract.check_and_lower(&resolver, &mut ty_ctx, &body);
                let subst = specification::subst_for_arguments(&body);

                out_contract.subst(&subst);

                // Basic clean up, replace FalseEdges with Gotos. Could potentially also replace other statement with Nops.
                // Investigate if existing MIR passes do this as part of 'post borrowck cleanup'.
                // TODO: now that we don't use polonius info: consider using optimized mir instead?
                RemoveFalseEdge { tcx }.visit_body(&mut body);
                let translated = FunctionTranslator::new(tcx, &mut ty_ctx, &body, resolver, def_id)
                    .translate(out_contract);

                ty_ctx.modules.add_module(translated);
            }
        }
    }

    use std::fs::File;

    let mut out: Box<dyn Write> = match output {
        Some(f) => Box::new(std::io::BufWriter::new(File::create(f)?)),
        None => Box::new(std::io::stdout()),
    };

    print_crate(&mut out, tcx.crate_name(LOCAL_CRATE).to_string().to_camel_case(), ty_ctx.modules)?;
    Ok(())
}
use std::io::Write;

// TODO: integrate crate name into the modules
fn print_crate<W>(out: &mut W, _name: String, krate: modules::Modules) -> std::io::Result<()>
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

fn sysroot_path() -> String {
    use std::process::Command;
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain")).unwrap();
    let channel = toolchain["toolchain"]["channel"].as_str().unwrap();

    let output = Command::new("rustup")
        .arg("run")
        .arg(channel)
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap();

    print!("{}", String::from_utf8(output.stderr).ok().unwrap());

    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

struct RemoveFalseEdge<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for RemoveFalseEdge<'tcx> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(&mut self, terminator: &mut Terminator<'tcx>, _location: Location) {
        if let rustc_middle::mir::TerminatorKind::FalseEdge { real_target, .. } = terminator.kind {
            terminator.kind = rustc_middle::mir::TerminatorKind::Goto { target: real_target }
        }
    }
}
