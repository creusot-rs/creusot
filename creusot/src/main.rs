#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![register_tool(creusot)]
#![feature(const_panic, or_patterns, iterator_fold_self)]

extern crate polonius_engine;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_resolve;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;

#[macro_use]
extern crate log;

use def_path_trie::DefPathTrie;
use mlcfg::Module;
use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_hir::{
    def_id::LOCAL_CRATE,
    Item,
};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{
    mir::{visit::MutVisitor, Location, Terminator},
    ty::{TyCtxt, WithOptConstParam},
};

mod analysis;

mod place;
mod translation;

#[allow(dead_code)]
mod debug;
mod mlcfg;

use rustc_session::Session;
use translation::*;

mod def_path_trie;

struct ToWhy {
    output_file: Option<String>,
}

impl Callbacks for ToWhy {
    // Register callback for after MIR borrowck and typechecking is finished
    fn after_analysis<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| translate(&self.output_file, c.session(), tcx))
            .unwrap();
        Compilation::Stop
    }
}

use std::env::args as get_args;
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

fn translate(output: &Option<String>, sess: &Session, tcx: TyCtxt) -> Result<()> {
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
                ty_decls.push((hir_map.local_def_id(*item_id).to_def_id(), item.span));
            }
        }
    }

    use def_path_trie::*;

    let mut translated_modules: DefPathTrie<Module> = DefPathTrie::new();

    // Type translation state, including which datatypes have already been translated.
    let mut ty_ctx = translation::ty::Ctx::new(tcx, sess);

    // Translate all type declarations and push them into the module collection
    for (def_id, span) in ty_decls.iter() {
        debug!("Translating type declaration {:?}", def_id);
        translation::ty::translate_tydecl(&mut ty_ctx, *span, *def_id);
    }

    'bodies: for def_id in tcx.body_owners() {
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

        // Parent module
        let module = util::module_of(tcx, def_id);

        let mut func_contract = (Vec::new(), Vec::new());

        let attrs = tcx.get_attrs(def_id);

        for attr in translation::util::spec_attrs(attrs) {
            match attr.path.segments[2].ident.name.to_string().as_ref() {
                "requires" => {
                    let req = ts_to_symbol(attr.args.inner_tokens()).unwrap();
                    func_contract.0.push(specification::requires_to_why(&body, req));
                    // func_contract.0.push(req);
                }
                "ensures" => {
                    let req = ts_to_symbol(attr.args.inner_tokens()).unwrap();
                    let ens_clause = specification::ensures_to_why(&body, req);
                    func_contract.1.push(ens_clause);
                }
                "invariant" => {
                    continue 'bodies; // this body is an invariant closure, skip it.
                }
                _ => unimplemented!(),
            }
        }

        // Basic clean up, replace FalseEdges with Gotos. Could potentially also replace other statement with Nops.
        // Investigate if existing MIR passes do this as part of 'post borrowck cleanup'.
        // TODO: now that we don't use polonius info: consider using optimized mir instead?
        RemoveFalseEdge { tcx }.visit_body(&mut body);

        let translated = FunctionTranslator::new(sess, tcx, &body).translate(def_id, func_contract);

        // debug::debug(tcx, &body);
        translated_modules.get_mut_with_default(module).functions.push(translated);
    }

    // Collect all the type translations
    ty_ctx.collect(&mut translated_modules);
    use std::fs::File;

    let mut out = match output {
        Some(f) => Box::new(std::io::BufWriter::new(File::create(f)?)) as Box<dyn Write>,
        None => Box::new(std::io::stdout()) as Box<dyn Write>,
    };
    writeln!(out, "module Ambient")?;
    writeln!(out, "{}", mlcfg::PRELUDE)?;
    print_module_tree(&mut out, &mut Vec::new(), &translated_modules).unwrap();
    writeln!(out, "end")?;
    Ok(())
}
use std::io::Write;

fn print_module_tree<W>(
    out: &mut W,
    open_scopes: &mut Vec<String>,
    mod_tree: &DefPathTrie<Module>,
) -> std::io::Result<()>
where
    W: Write,
{
    use heck::CamelCase;

    let indent_level = (open_scopes.len() + 1) * 2;

    for (k, child) in mod_tree.children_with_keys() {
        let scope_name = k.to_string()[..].to_camel_case();

        writeln!(out, "{:ident$}scope {}", "", scope_name, ident = indent_level)?;
        open_scopes.push(scope_name);
        print_module_tree(out, open_scopes, child)?;
        open_scopes.pop();
        writeln!(out, "{:ident$}end", "", ident = indent_level)?;
    }

    let fe = mlcfg::printer::FormatEnv { indent: indent_level, scope: &open_scopes[..] };

    let module = mod_tree.value().unwrap();

    for ty_decl in &module.tydecls {
        writeln!(out, "{}", fe.to(ty_decl))?;
    }

    for pred in &module.predicates {
        writeln!(out, "{}", fe.to(pred))?;
    }

    for func in &module.functions {
        writeln!(out, "{}", fe.to(func))?;
    }
    Ok(())
}


fn sysroot_path() -> String {
    use std::process::Command;
    let toolchain = include_str!("../../rust-toolchain").trim();
    let output = Command::new("rustup")
        .arg("run")
        .arg(toolchain)
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap();

    print!("{}", String::from_utf8(output.stderr).ok().unwrap());

    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

use rustc_ast::{
    token::TokenKind::Literal,
    tokenstream::{TokenStream, TokenTree::*},
};

fn ts_to_symbol(ts: TokenStream) -> Option<String> {
    assert_eq!(ts.len(), 1);

    if let Token(tok) = ts.trees().next().unwrap() {
        if let Literal(lit) = tok.kind {
            return Some(unescape::unescape(&lit.symbol.as_str())?.to_string());
        }
    }
    None
}

struct RemoveFalseEdge<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for RemoveFalseEdge<'tcx> {
    fn tcx<'a>(&'a self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_terminator(&mut self, terminator: &mut Terminator<'tcx>, _location: Location) {
        match terminator.kind {
            rustc_middle::mir::TerminatorKind::FalseEdge { real_target, .. } => {
                terminator.kind = rustc_middle::mir::TerminatorKind::Goto { target: real_target }
            }
            _ => {}
        }
    }
}
