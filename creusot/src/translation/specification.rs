use std::collections::HashMap;

use crate::translation::function::real_locals;
use crate::{ctx::*, util};
use rustc_macros::{TyDecodable, TyEncodable};
use rustc_middle::thir::{self, ExprKind, Thir};
use rustc_middle::ty::subst::InternalSubsts;
use why3::declaration::Contract;
use why3::mlcfg::Exp;
use why3::Ident;

use self::typing::pearlite_stub;

use super::LocalIdent;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Location};
use rustc_middle::ty::{self, TyCtxt};

mod builtins;
mod lower;
pub mod typing;

pub use lower::*;

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct PreContract {
    pub func_id: DefId,
    variant: Option<DefId>,
    requires: Vec<DefId>,
    ensures: Vec<DefId>,
}

impl PreContract {
    pub fn new(func_id: DefId) -> Self {
        Self { func_id, variant: None, requires: Vec::new(), ensures: Vec::new() }
    }

    pub fn iter_items(&self) -> impl Iterator<Item = DefId> + '_ {
        self.variant
            .iter()
            .cloned()
            .chain(self.requires.iter().cloned())
            .chain(self.ensures.iter().cloned())
    }

    pub fn check_and_lower<'tcx>(
        self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        _: DefId,
    ) -> Contract {
        let mut out = Contract::new();
        let subst = InternalSubsts::identity_for_item(ctx.tcx, self.func_id);

        use crate::rustc_middle::ty::subst::Subst;
        for req_id in self.requires {
            log::debug!("require clause {:?}", req_id);
            let term = ctx.term(req_id).unwrap().clone().subst(ctx.tcx, subst);
            out.requires.push(lower_pure(ctx, names, req_id, term));
        }

        for ens_id in self.ensures {
            log::debug!("ensures clause {:?}", ens_id);
            let term = ctx.term(ens_id).unwrap().clone().subst(ctx.tcx, subst);
            out.ensures.push(lower_pure(ctx, names, ens_id, term));
        }

        if let Some(var_id) = self.variant {
            log::debug!("variant clause {:?}", var_id);
            let term = ctx.term(var_id).unwrap().clone().subst(ctx.tcx, subst);
            out.variant = vec![lower_pure(ctx, names, var_id, term)];
        };

        if let Some(extern_spec) = ctx.extern_spec(self.func_id) {
            let subst = extern_spec
                .subst
                .iter()
                .map(|(i, i2)| {
                    (Ident::build(i.as_str()), Exp::impure_var(Ident::build(i2.as_str())))
                })
                .collect();
            out.subst(&subst);
        }
        out
    }

    pub fn iter_ids(&self) -> impl Iterator<Item = DefId> + '_ {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter()).cloned()
    }
}

// Turn a typing context into a substition.
pub fn inv_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loc: Location,
) -> HashMap<why3::Ident, Exp> {
    use rustc_middle::mir::VarDebugInfoContents::Place;
    let local_map = real_locals(tcx, body);
    let mut scope = body.source_info(loc).scope;

    let mut args = HashMap::new();
    loop {
        for var_info in &body.var_debug_info {
            if var_info.source_info.scope != scope {
                continue;
            }

            let loc = match var_info.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!(),
            };
            let loc = local_map[&loc];
            let source_name = var_info.name.to_string();
            args.entry(source_name.into())
                .or_insert_with(|| Exp::pure_var(LocalIdent::dbg(loc, var_info).ident()));
        }

        if let Some(parent) = body.source_scopes[scope].parent_scope {
            scope = parent
        } else {
            break;
        }
    }

    return args;
}

#[derive(Debug)]
pub enum SpecAttrError {
    InvalidTokens { id: DefId },
    InvalidTerm { id: DefId },
}

pub fn contract_of(ctx: &mut TranslationCtx, def_id: DefId) -> Result<PreContract, SpecAttrError> {
    use SpecAttrError::*;

    if let Some(extern_spec) = ctx.extern_spec(def_id).cloned() {
        return Ok(extern_spec.contract);
    }

    let attrs = ctx.tcx.get_attrs_unchecked(def_id);
    let mut contract = PreContract::new(def_id);

    for attr in attrs {
        if !util::is_attr(attr, "spec") {
            continue;
        }

        let attr = attr.get_normal_item();
        use rustc_ast::ast::{MacArgs, MacArgsEq};

        // Stop using diagnostic item.
        // Use a custom HIR visitor which walks the attributes
        match attr.path.segments[2].ident.to_string().as_str() {
            "requires" => {
                let req_name = match &attr.args {
                    MacArgs::Eq(_, MacArgsEq::Hir(l)) => l.token.symbol,
                    _ => return Err(InvalidTokens { id: def_id }),
                };
                let req_id = ctx.creusot_item(req_name).ok_or(InvalidTerm { id: def_id })?;
                contract.requires.push(req_id);
            }
            "ensures" => {
                let ens_name = match &attr.args {
                    MacArgs::Eq(_, MacArgsEq::Hir(l)) => l.token.symbol,
                    _ => return Err(InvalidTokens { id: def_id }),
                };
                let ens_id = ctx.creusot_item(ens_name).ok_or(InvalidTerm { id: def_id })?;
                contract.ensures.push(ens_id);
            }
            "variant" => {
                let var_name = match &attr.args {
                    MacArgs::Eq(_, MacArgsEq::Hir(l)) => l.token.symbol,
                    _ => return Err(InvalidTokens { id: def_id }),
                };
                let var_id = ctx.creusot_item(var_name).ok_or(InvalidTerm { id: def_id })?;
                contract.variant = Some(var_id);
            }
            _ => {}
        }
    }

    Ok(contract)
}

struct PurityVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
}

impl PurityVisitor<'_, '_> {
    fn is_overloaded_item(&self, def_id: DefId) -> bool {
        let def_path = self.tcx.def_path_str(def_id);

        def_path == "std::ops::Index::index"
            || def_path == "std::convert::Into::into"
            || def_path == "std::convert::From::from"
            || def_path == "std::ops::Mul::mul"
            || def_path == "std::ops::Add::add"
            || def_path == "std::ops::Sub::sub"
            || def_path == "std::ops::Div::div"
            || def_path == "std::ops::Rem::rem"
            || def_path == "std::ops::Neg::neg"
            || def_path == "std::boxed::Box::<T>::new"
    }
}

impl<'a, 'tcx> thir::visit::Visitor<'a, 'tcx> for PurityVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &thir::Expr<'tcx>) {
        match expr.kind {
            ExprKind::Call { fun, .. } => {
                if let &ty::FnDef(func_did, _) = self.thir[fun].ty.kind() {
                    if !util::is_predicate(self.tcx, func_did)
                        && !util::is_logic(self.tcx, func_did)
                        && !util::get_builtin(self.tcx, func_did).is_some()
                        && !pearlite_stub(self.tcx, self.thir[fun].ty).is_some()
                        && !self.is_overloaded_item(func_did)
                    {
                        self.tcx.sess.span_err_with_code(
                            self.thir[fun].span,
                            "called impure program function in logical context",
                            rustc_errors::DiagnosticId::Error(String::from("creusot")),
                        );
                    }
                } else {
                    self.tcx.sess.span_fatal_with_code(
                        expr.span,
                        "non function call in logical context",
                        rustc_errors::DiagnosticId::Error(String::from("creusot")),
                    )
                }
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr)
    }
}
