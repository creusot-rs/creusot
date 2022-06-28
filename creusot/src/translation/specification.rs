use self::typing::{pearlite_stub, Term};
use super::LocalIdent;
use crate::{ctx::*, util, util::closure_owner};
use creusot_rustc::{
    hir::def_id::DefId,
    macros::{TyDecodable, TyEncodable, TypeFoldable},
    middle::{
        mir::OUTERMOST_SOURCE_SCOPE,
        thir::{self, ExprKind, Thir},
        ty::{
            self,
            subst::{InternalSubsts, SubstsRef},
            EarlyBinder, Subst, TyCtxt,
        },
    },
    smir::mir::{Body, Local, Location, SourceScope},
    span::Symbol,
};
use std::collections::{HashMap, HashSet};
use why3::{declaration::Contract, exp::Exp, Ident};

mod builtins;
mod lower;
pub mod typing;

pub use lower::*;

#[derive(Clone, Debug, Default, TypeFoldable)]
pub struct PreContract<'tcx> {
    variant: Option<Term<'tcx>>,
    requires: Vec<Term<'tcx>>,
    ensures: Vec<Term<'tcx>>,
}

impl<'tcx> PreContract<'tcx> {
    pub fn to_exp(
        self,
        ctx: &mut TranslationCtx<'_, 'tcx>,
        names: &mut CloneMap<'tcx>,
        id: DefId,
    ) -> Contract {
        let mut out = Contract::new();
        let param_env = ctx.param_env(closure_owner(ctx.tcx, id));

        for term in self.requires {
            out.requires.push(lower_pure(ctx, names, id, param_env, term));
        }
        for term in self.ensures {
            out.ensures.push(lower_pure(ctx, names, id, param_env, term));
        }

        if let Some(term) = self.variant {
            out.variant = vec![lower_pure(ctx, names, id, param_env, term)];
        }

        if let Some(extern_spec) = ctx.extern_spec(id) {
            let subst = extern_spec
                .arg_subst
                .iter()
                .map(|(i, i2)| {
                    (Ident::build(i.as_str()), Exp::impure_var(Ident::build(i2.as_str())))
                })
                .collect();
            out.subst(&subst);
        }
        out
    }

    pub fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty() && self.variant.is_none()
    }
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct ContractClauses {
    variant: Option<DefId>,
    requires: Vec<DefId>,
    ensures: Vec<DefId>,
}

impl ContractClauses {
    pub fn new() -> Self {
        Self { variant: None, requires: Vec::new(), ensures: Vec::new() }
    }

    fn get_pre<'tcx>(self, ctx: &mut TranslationCtx<'_, 'tcx>) -> EarlyBinder<PreContract<'tcx>> {
        let mut out = PreContract::default();
        for req_id in self.requires {
            log::debug!("require clause {:?}", req_id);
            let term = ctx.term(req_id).unwrap().clone();
            out.requires.push(term);
        }

        for ens_id in self.ensures {
            log::debug!("ensures clause {:?}", ens_id);
            let term = ctx.term(ens_id).unwrap().clone();
            out.ensures.push(term);
        }

        if let Some(var_id) = self.variant {
            log::debug!("variant clause {:?}", var_id);
            let term = ctx.term(var_id).unwrap().clone();
            out.variant = Some(term);
        };
        EarlyBinder(out)
    }

    pub fn iter_ids(&self) -> impl Iterator<Item = DefId> + '_ {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter()).cloned()
    }
}

struct ScopeTree(HashMap<SourceScope, (HashSet<(Symbol, Local)>, Option<SourceScope>)>);

impl ScopeTree {
    fn build<'tcx>(body: &Body<'tcx>) -> Self {
        use creusot_rustc::smir::mir::VarDebugInfoContents::Place;
        let mut scope_tree: HashMap<SourceScope, (HashSet<_>, Option<_>)> = Default::default();

        for var_info in &body.var_debug_info {
            // All variables in the DebugVarInfo should be user variables and thus be just locals
            let loc = match var_info.value {
                Place(p) => p.as_local().unwrap(),
                _ => panic!(),
            };
            let info = var_info.source_info;

            let scope = info.scope;
            let scope_data = &body.source_scopes[scope];

            let entry = scope_tree.entry(scope).or_default();

            let name = var_info.name;
            entry.0.insert((name, loc));

            if let Some(parent) = scope_data.parent_scope {
                entry.1 = Some(parent);
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }

        for (scope, scope_data) in body.source_scopes.iter_enumerated() {
            if let Some(parent) = scope_data.parent_scope {
                scope_tree.entry(scope).or_default().1 = Some(parent);
                scope_tree.entry(parent).or_default();
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }
        ScopeTree(scope_tree)
    }

    fn visible_locals(&self, scope: SourceScope) -> HashMap<Symbol, Local> {
        let mut locals = HashMap::new();
        let mut to_visit = Some(scope);

        while let Some(s) = to_visit.take() {
            self.0[&s].0.iter().for_each(|(id, loc)| {
                locals.entry(*id).or_insert(*loc);
            });
            to_visit = self.0[&s].1.clone();
        }

        locals
    }
}

// Turn a typing context into a substition.
pub fn inv_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    loc: Location,
) -> HashMap<why3::Ident, Exp> {
    // let local_map = real_locals(tcx, body);
    let info = body.source_info(loc);
    let mut args = HashMap::new();

    let tree = ScopeTree::build(body);

    for (k, v) in tree.visible_locals(info.scope) {
        let loc = v;
        args.insert(k.to_string().into(), Exp::pure_var(LocalIdent::dbg_raw(loc, k).ident()));
    }

    return args;
}

#[derive(Debug)]
pub enum SpecAttrError {
    InvalidTokens { id: DefId },
    InvalidTerm { id: DefId },
}

pub(crate) fn contract_clauses_of(
    ctx: &TranslationCtx,
    def_id: DefId,
) -> Result<ContractClauses, SpecAttrError> {
    use SpecAttrError::*;

    let attrs = ctx.get_attrs_unchecked(def_id);
    let mut contract = ContractClauses::new();

    // Attributes are given in reverse order. So we need to rever the list of
    // attributes to make sure requires/ensures clauses appear in the same
    // order in WhyML code as they appear in Rust code.
    for attr in attrs.iter().rev() {
        if !util::is_attr(attr, "spec") {
            continue;
        }

        let attr = attr.get_normal_item();
        use creusot_rustc::ast::ast::{MacArgs, MacArgsEq};

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

pub fn inherited_extern_spec<'tcx>(
    ctx: &TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    let subst = InternalSubsts::identity_for_item(ctx.tcx, def_id);
    try {
        if def_id.is_local() || ctx.extern_spec(def_id).is_some() {
            return None;
        }

        let assoc = ctx.opt_associated_item(def_id)?;
        let trait_ref = ctx.impl_trait_ref(assoc.container.id())?;
        let id = assoc.trait_item_def_id?;

        if ctx.extern_spec(id).is_none() {
            return None;
        }
        (id, EarlyBinder(trait_ref.substs).subst(ctx.tcx, subst))
    }
}

pub fn contract_of<'tcx>(ctx: &mut TranslationCtx<'_, 'tcx>, def_id: DefId) -> PreContract<'tcx> {
    if let Some(extern_spec) = ctx.extern_spec(def_id).cloned() {
        extern_spec.contract.get_pre(ctx).subst(ctx.tcx, extern_spec.subst)
    } else {
        if let Some((def_id, subst)) = inherited_extern_spec(ctx, def_id) {
            ctx.extern_spec(def_id).cloned().unwrap().contract.get_pre(ctx).subst(ctx.tcx, subst)
        } else {
            let subst = InternalSubsts::identity_for_item(ctx.tcx, def_id);
            contract_clauses_of(ctx, def_id).unwrap().get_pre(ctx).subst(ctx.tcx, subst)
        }
    }
}

// These methods are allowed to cheat the purity restrictions because they are lang items we cannot redefine
pub fn is_overloaded_item(tcx: TyCtxt, def_id: DefId) -> bool {
    let def_path = tcx.def_path_str(def_id);

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
        || def_path == "std::ops::Deref::deref"
        || def_path == "std::clone::Clone::clone"
}

struct PurityVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    thir: &'a Thir<'tcx>,
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
                        && !is_overloaded_item(self.tcx, func_did)
                    {
                        self.tcx.sess.span_err_with_code(
                            self.thir[fun].span,
                            &format!(
                                "called impure program function in logical context {:?}",
                                self.tcx.def_path_str(func_did)
                            ),
                            creusot_rustc::errors::DiagnosticId::Error(String::from("creusot")),
                        );
                    }
                } else {
                    self.tcx.sess.span_fatal_with_code(
                        expr.span,
                        "non function call in logical context",
                        creusot_rustc::errors::DiagnosticId::Error(String::from("creusot")),
                    )
                }
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr)
    }
}
