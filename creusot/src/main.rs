#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![register_tool(creusot)]
#![feature(const_panic, or_patterns)]

extern crate polonius_engine;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_serialize;
extern crate rustc_span;
extern crate rustc_target;

use mlcfg::{Function, MlTyDecl};
use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_hir::{
    def_id::{DefId, LOCAL_CRATE},
    definitions::DefPathData,
    Item,
};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::{
    mir::{visit::MutVisitor, Location, Terminator},
    ty::{TyCtxt, WithOptConstParam},
};

mod place;
use place::*;

mod translation;

// use translation::specification::SpecificationTranslator;
use translation::*;
mod analysis;

#[allow(dead_code)]
mod polonius;

#[allow(dead_code)]
mod debug;
mod mlcfg;

struct ToWhy {}

// use polonius_facts::FactLoader;
// use polonius_engine::{Algorithm, Output};

impl Callbacks for ToWhy {
    // Register callback for after MIR borrowck and typechecking is finished
    fn after_analysis<'tcx>(&mut self, _c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries.global_ctxt().unwrap().peek_mut().enter(translate).unwrap();
        Compilation::Stop
    }
}

use std::{collections::HashMap, env::args as get_args};
fn main() {
    env_logger::init();
    // env_logger::init_from_env(
    // env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "debug"));
    let mut args = get_args().collect::<Vec<String>>();
    // args.push("-Znll-facts".to_owned());
    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    args.push("-Znll-facts".to_owned());
    // args.push("-Zdump-mir=".to_owned());
    RunCompiler::new(&args, &mut ToWhy {}).run().unwrap();
}

use std::io::Result;

fn is_type_decl(item: &Item) -> bool {
    match item.kind {
        rustc_hir::ItemKind::TyAlias(_, _) => true,
        rustc_hir::ItemKind::OpaqueTy(_) => unimplemented!(),
        rustc_hir::ItemKind::Enum(_, _) => true,
        rustc_hir::ItemKind::Struct(_, _) => true,
        rustc_hir::ItemKind::Union(_, _) => unimplemented!(),
        _ => false,
    }
}

fn translate(tcx: TyCtxt) -> Result<()> {
    let hir_map = tcx.hir();

    // Collect the DefIds of all type declarations in this crate
    let mut ty_decls = Vec::new();

    for (_, mod_items) in tcx.hir_crate(LOCAL_CRATE).modules.iter() {
        for item_id in mod_items.items.iter() {
            let item = hir_map.item(*item_id);
            // What about inline type declarations?
            // How do we find those?
            if is_type_decl(item) {
                ty_decls.push(hir_map.local_def_id(*item_id).to_def_id());
            }
        }
    }

    type MlModule = (Vec<MlTyDecl>, Vec<Function>);
    let mut translated_modules: HashMap<_, MlModule> = HashMap::new();

    // Translate all type declarations and push them into the module collection
    for def_id in ty_decls.iter() {
        log::debug!("Translating type declaration {:?}", def_id);
        let adt = tcx.adt_def(*def_id);
        let res = translation::translate_tydecl(tcx, adt);

        let module = module_of(tcx, *def_id);
        translated_modules.entry(module).or_default().0.push(res);
    }

    'bodies: for def_id in tcx.body_owners() {
        log::debug!("Translating body {:?}", def_id);
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
        let module = module_of(tcx, def_id);

        let mut func_contract = (Vec::new(), Vec::new());

        let attrs = tcx.get_attrs(def_id);

        for attr in translation::util::spec_attrs(attrs) {
            match attr.path.segments[2].ident.name.to_string().as_ref() {
                "requires" => {
                    let req = ts_to_symbol(attr.args.inner_tokens());
                    func_contract.0.push(specification::requires_to_why(&body, req));
                    // func_contract.0.push(req);
                }
                "ensures" => {
                    let req = ts_to_symbol(attr.args.inner_tokens());
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

        let translated = FunctionTranslator::new(tcx, &body).translate(def_id, func_contract);

        // debug::debug(tcx, &body, polonius_info);
        translated_modules.entry(module).or_default().1.push(translated);
    }

    for (modk, (ty, funcs)) in translated_modules.iter() {
        let def_path = tcx.def_path(*modk);
        let mut opened_scopes = 0;
        if def_path.data.is_empty() {
            // main module
            println!("module Main");
            opened_scopes = 1;
        } else {
            // other modules // filter out closure path elements
            for seg in def_path.data[0..def_path.data.len() - 1].iter() {
                println!("scope {}", seg);
                opened_scopes += 1;
            }

            println!("module {}", def_path.data.last().unwrap());
            opened_scopes += 1;
        }

        use itertools::*;
        println!("{}", ty.iter().format("\n"));
        println!("{}", funcs.iter().format("\n"));

        for _ in 0..opened_scopes {
            println!("end");
        }
    }

    Ok(())
}

fn module_of<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> DefId {
    let mut def_key = tcx.def_key(def_id);
    let mut module = def_id;
    let mut layers = 1;

    while layers > 0 {
        match def_key.disambiguated_data.data {
            DefPathData::ClosureExpr => layers += 1,
            _ => {}
        }
        let def_id = DefId { krate: LOCAL_CRATE, index: def_key.parent.unwrap() };
        def_key = tcx.def_key(def_id);
        module = def_id;
        layers -= 1
    }

    module
}

use rustc_ast::{
    token::TokenKind::Literal,
    tokenstream::{TokenStream, TokenTree::*},
};

fn ts_to_symbol(ts: TokenStream) -> String {
    assert_eq!(ts.len(), 1);

    if let Token(tok) = ts.trees().next().unwrap() {
        if let Literal(lit) = tok.kind {
            return lit.symbol.to_string();
        }
    }
    panic!("not a single token")
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
