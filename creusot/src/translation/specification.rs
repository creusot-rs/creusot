use super::{
    pearlite::{normalize, pearlite_stub, Term, TermKind},
    LocalIdent,
};
use crate::{ctx::*, util, util::closure_owner};
use creusot_rustc::{
    hir::def_id::DefId,
    macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable},
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
use rustc_middle::ty::ParamEnv;
use std::collections::{HashMap, HashSet};
use why3::declaration::Contract;

pub(crate) use crate::backend::term::*;

#[derive(Clone, Debug, Default, TypeFoldable, TypeVisitable)]
pub struct PreContract<'tcx> {
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) requires: Vec<Term<'tcx>>,
    pub(crate) ensures: Vec<Term<'tcx>>,
    pub(crate) may_panic: Option<Term<'tcx>>,
}

impl<'tcx> PreContract<'tcx> {
    pub(crate) fn subst(&mut self, subst: &HashMap<Symbol, Term<'tcx>>) {
        for term in self.terms_mut() {
            term.subst(subst);
        }

        for v in &mut self.may_panic {
            v.subst(subst);
        }
    }

    pub(crate) fn normalize(mut self, tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>) -> Self {
        for term in self.terms_mut() {
            normalize(tcx, param_env, term);
        }
        self
    }

    pub(crate) fn to_exp(
        self,
        ctx: &mut TranslationCtx<'tcx>,
        names: &mut CloneMap<'tcx>,
        id: DefId,
    ) -> Contract {
        let mut out = Contract::new();
        let param_env = ctx.param_env(closure_owner(ctx.tcx, id));

        for term in self.requires {
            out.requires.push(lower_pure(ctx, names, param_env, term));
        }
        for term in self.ensures {
            out.ensures.push(lower_pure(ctx, names, param_env, term));
        }

        if let Some(term) = self.variant {
            out.variant = vec![lower_pure(ctx, names, param_env, term)];
        }

        if let Some(term) = self.may_panic {
            out.may_panic = Some(lower_pure(ctx, names, param_env, term));
        }

        out
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty() && self.variant.is_none() && self.may_panic.is_none()
    }

    #[allow(dead_code)]
    pub(crate) fn terms(&self) -> impl Iterator<Item = &Term<'tcx>> {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter()).chain(self.may_panic.iter())
    }

    fn terms_mut(&mut self) -> impl Iterator<Item = &mut Term<'tcx>> {
        self.requires.iter_mut().chain(self.ensures.iter_mut()).chain(self.variant.iter_mut()).chain(self.may_panic.iter_mut())
    }

    pub(crate) fn ensures_conj(&self, tcx: TyCtxt<'tcx>) -> Term<'tcx> {
        let mut ensures = self.ensures.clone();

        let postcond = ensures.pop().unwrap_or(Term::mk_true(tcx));
        let postcond = ensures.into_iter().rfold(postcond, Term::conj);
        postcond
    }

    pub(crate) fn requires_conj(&self, tcx: TyCtxt<'tcx>) -> Term<'tcx> {
        let mut requires = self.requires.clone();

        let precond = requires.pop().unwrap_or(Term::mk_true(tcx));
        let precond = requires.into_iter().rfold(precond, Term::conj);
        precond
    }
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub struct ContractClauses {
    variant: Option<DefId>,
    requires: Vec<DefId>,
    ensures: Vec<DefId>,
    may_panic: Option<DefId>,
}

impl ContractClauses {
    pub(crate) fn new() -> Self {
        Self { variant: None, requires: Vec::new(), ensures: Vec::new(), may_panic: None }
    }

    fn get_pre<'tcx>(self, ctx: &mut TranslationCtx<'tcx>) -> EarlyBinder<PreContract<'tcx>> {
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

        if let Some(var_id) = self.may_panic {
            log::debug!("may_panic clause {:?}", var_id);
            let term = ctx.term(var_id).unwrap().clone();
            out.may_panic = Some(term);
        }

        EarlyBinder(out)
    }

    pub(crate) fn iter_ids(&self) -> impl Iterator<Item = DefId> + '_ {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter()).chain(self.may_panic.iter()).cloned()
    }
}

#[derive(Debug)]
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
            let d = (HashSet::new(), None);
            self.0.get(&s).unwrap_or_else(|| &d).0.iter().for_each(|(id, loc)| {
                locals.entry(*id).or_insert(*loc);
            });
            to_visit = self.0.get(&s).unwrap_or_else(|| &d).1.clone();
        }

        locals
    }
}

// Turn a typing context into a substition.
pub(crate) fn inv_subst<'tcx>(body: &Body<'tcx>, loc: Location) -> HashMap<Symbol, Term<'tcx>> {
    // let local_map = real_locals(tcx, body);
    let info = body.source_info(loc);
    let mut args = HashMap::new();

    let tree = ScopeTree::build(body);

    for (k, v) in tree.visible_locals(info.scope) {
        let loc = v;
        let ty = body.local_decls[loc].ty;
        let span = body.local_decls[loc].source_info.span;
        args.insert(
            k,
            Term { ty, span, kind: TermKind::Var(LocalIdent::dbg_raw(loc, k).symbol()) },
        );
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
        let get_creusot_item = || {
            let predicate_name = match &attr.args {
                MacArgs::Eq(_, MacArgsEq::Hir(l)) => l.token_lit.symbol,
                _ => return Err(InvalidTokens { id: def_id }),
            };
            ctx.creusot_item(predicate_name).ok_or(InvalidTerm { id: def_id })
        };

        match attr.path.segments[2].ident.to_string().as_str() {
            "requires" => contract.requires.push(get_creusot_item()?),
            "ensures" => contract.ensures.push(get_creusot_item()?),
            "variant" => contract.variant = Some(get_creusot_item()?),
            "may_panic" => contract.may_panic = Some(get_creusot_item()?),
            _ => {}
        }
    }

    Ok(contract)
}

pub(crate) fn inherited_extern_spec<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    let subst = InternalSubsts::identity_for_item(ctx.tcx, def_id);
    try {
        if def_id.is_local() || ctx.extern_spec(def_id).is_some() {
            return None;
        }

        let assoc = ctx.opt_associated_item(def_id)?;
        let trait_ref = ctx.impl_trait_ref(assoc.container_id(ctx.tcx))?;
        let id = assoc.trait_item_def_id?;

        if ctx.extern_spec(id).is_none() {
            return None;
        }
        (id, EarlyBinder(trait_ref.substs).subst(ctx.tcx, subst))
    }
}

pub(crate) fn contract_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> PreContract<'tcx> {
    if let Some(extern_spec) = ctx.extern_spec(def_id).cloned() {
        let mut contract = extern_spec.contract.get_pre(ctx).subst(ctx.tcx, extern_spec.subst);
        contract.subst(&extern_spec.arg_subst.iter().cloned().collect());
        contract.normalize(ctx.tcx, ctx.param_env(def_id))
    } else {
        if let Some((parent_id, subst)) = inherited_extern_spec(ctx, def_id) {
            let spec = ctx.extern_spec(parent_id).cloned().unwrap();
            let mut contract = spec.contract.get_pre(ctx).subst(ctx.tcx, subst);
            contract.subst(&spec.arg_subst.iter().cloned().collect());
            contract.normalize(ctx.tcx, ctx.param_env(def_id))
        } else {
            let subst = InternalSubsts::identity_for_item(ctx.tcx, def_id);
            contract_clauses_of(ctx, def_id).unwrap().get_pre(ctx).subst(ctx.tcx, subst)
        }
    }
}

// These methods are allowed to cheat the purity restrictions because they are lang items we cannot redefine
pub(crate) fn is_overloaded_item(tcx: TyCtxt, def_id: DefId) -> bool {
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

pub(crate) struct PurityVisitor<'a, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) thir: &'a Thir<'tcx>,
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
