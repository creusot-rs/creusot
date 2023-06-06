use super::{
    fmir::LocalDecls,
    pearlite::{normalize, pearlite_stub, Literal, Term, TermKind},
};
use crate::{ctx::*, util};
use rustc_ast::ast::{AttrArgs, AttrArgsEq};
use rustc_hir::def_id::DefId;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{Body, Local, SourceInfo, SourceScope, OUTERMOST_SOURCE_SCOPE},
    thir::{self, ExprKind, Thir},
    ty::{
        self,
        subst::{InternalSubsts, SubstsRef},
        EarlyBinder, ParamEnv, TyCtxt,
    },
};
use rustc_span::Symbol;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, Default, TypeFoldable, TypeVisitable)]
pub struct PreContract<'tcx> {
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) requires: Vec<Term<'tcx>>,
    pub(crate) ensures: Vec<Term<'tcx>>,
}

impl<'tcx> PreContract<'tcx> {
    pub(crate) fn subst(&mut self, subst: &HashMap<Symbol, Term<'tcx>>) {
        for term in self.terms_mut() {
            term.subst(subst);
        }
    }

    pub(crate) fn normalize(mut self, tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>) -> Self {
        for term in self.terms_mut() {
            normalize(tcx, param_env, term);
        }
        self
    }

    // A bit of a hack used to see if an external function has no contract
    pub(crate) fn is_false(&self) -> bool {
        self.requires.len() == 1
            && matches!(self.requires[0].kind, TermKind::Lit(Literal::Bool(false)))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.requires.is_empty() && self.ensures.is_empty() && self.variant.is_none()
    }

    #[allow(dead_code)]
    pub(crate) fn terms(&self) -> impl Iterator<Item = &Term<'tcx>> {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter())
    }

    fn terms_mut(&mut self) -> impl Iterator<Item = &mut Term<'tcx>> {
        self.requires.iter_mut().chain(self.ensures.iter_mut()).chain(self.variant.iter_mut())
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
}

impl ContractClauses {
    pub(crate) fn new() -> Self {
        Self { variant: None, requires: Vec::new(), ensures: Vec::new() }
    }

    fn get_pre<'tcx>(self, ctx: &mut TranslationCtx<'tcx>) -> EarlyBinder<PreContract<'tcx>> {
        let mut out = PreContract::default();
        for req_id in self.requires {
            log::trace!("require clause {:?}", req_id);
            let term = ctx.term(req_id).unwrap().clone();
            out.requires.push(term);
        }

        for ens_id in self.ensures {
            log::trace!("ensures clause {:?}", ens_id);
            let term = ctx.term(ens_id).unwrap().clone();
            out.ensures.push(term);
        }

        if let Some(var_id) = self.variant {
            log::trace!("variant clause {:?}", var_id);
            let term = ctx.term(var_id).unwrap().clone();
            out.variant = Some(term);
        };
        EarlyBinder(out)
    }

    pub(crate) fn iter_ids(&self) -> impl Iterator<Item = DefId> + '_ {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter()).cloned()
    }
}

#[derive(Debug)]
struct ScopeTree(HashMap<SourceScope, (HashSet<(Symbol, Local)>, Option<SourceScope>)>);

impl ScopeTree {
    fn build<'tcx>(body: &Body<'tcx>) -> Self {
        use rustc_middle::mir::VarDebugInfoContents::Place;
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
pub(crate) fn inv_subst<'tcx>(
    body: &Body<'tcx>,
    locals: &LocalDecls<'tcx>,
    info: SourceInfo,
) -> HashMap<Symbol, Term<'tcx>> {
    // let local_map = real_locals(tcx, body);
    let mut args = HashMap::new();

    let tree = ScopeTree::build(body);

    for (k, v) in tree.visible_locals(info.scope) {
        let loc = v;
        let ty = body.local_decls[loc].ty;
        let span = body.local_decls[loc].source_info.span;
        args.insert(k, Term { ty, span, kind: TermKind::Var(locals[&loc].0.symbol()) });
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
        if !util::is_attr(attr, "clause") {
            continue;
        }

        let attr = attr.get_normal_item();

        // Stop using diagnostic item.
        // Use a custom HIR visitor which walks the attributes
        let get_creusot_item = || {
            let predicate_name = match &attr.args {
                AttrArgs::Eq(_, AttrArgsEq::Hir(l)) => l.symbol,
                _ => return Err(InvalidTokens { id: def_id }),
            };
            ctx.creusot_item(predicate_name).ok_or(InvalidTerm { id: def_id })
        };

        match attr.path.segments[2].ident.to_string().as_str() {
            "requires" => contract.requires.push(get_creusot_item()?),
            "ensures" => contract.ensures.push(get_creusot_item()?),
            "variant" => contract.variant = Some(get_creusot_item()?),
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
        (id, trait_ref.subst(ctx.tcx, subst).substs)
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
    } else if let Some((parent_id, subst)) = inherited_extern_spec(ctx, def_id) {
        let spec = ctx.extern_spec(parent_id).cloned().unwrap();
        let mut contract = spec.contract.get_pre(ctx).subst(ctx.tcx, subst);
        contract.subst(&spec.arg_subst.iter().cloned().collect());
        contract.normalize(ctx.tcx, ctx.param_env(def_id))
    } else {
        let subst = InternalSubsts::identity_for_item(ctx.tcx, def_id);
        let mut contract =
            contract_clauses_of(ctx, def_id).unwrap().get_pre(ctx).subst(ctx.tcx, subst);

        if contract.is_empty()
            && ctx.externs.get(def_id.krate).is_some()
            && util::item_type(ctx.tcx, def_id) == ItemType::Program
        {
            contract.requires.push(Term::mk_false(ctx.tcx));
        }

        contract
    }
}

// These methods are allowed to cheat the purity restrictions because they are lang items we cannot redefine
pub(crate) fn is_overloaded_item(tcx: TyCtxt, def_id: DefId) -> bool {
    let def_path = tcx.def_path_str(def_id);

    def_path.ends_with("::ops::Index::index")
        || def_path.ends_with("::convert::Into::into")
        || def_path.ends_with("::convert::From::from")
        || def_path.ends_with("::ops::Mul::mul")
        || def_path.ends_with("::ops::Add::add")
        || def_path.ends_with("::ops::Sub::sub")
        || def_path.ends_with("::ops::Div::div")
        || def_path.ends_with("::ops::Rem::rem")
        || def_path.ends_with("::ops::Neg::neg")
        || def_path.ends_with("::boxed::Box::<T>::new")
        || def_path.ends_with("::ops::Deref::deref")
        || def_path.ends_with("::clone::Clone::clone")
        || def_path.ends_with("Ghost::<T>::from_fn")
}

pub(crate) struct PurityVisitor<'a, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) thir: &'a Thir<'tcx>,
    pub(crate) in_pure_ctx: bool,
}

impl<'a, 'tcx> PurityVisitor<'a, 'tcx> {
    fn is_pure(&self, fun: thir::ExprId, func_did: DefId) -> bool {
        util::is_predicate(self.tcx, func_did)
            || util::is_logic(self.tcx, func_did)
            || util::get_builtin(self.tcx, func_did).is_some()
            || pearlite_stub(self.tcx, self.thir[fun].ty).is_some()
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
                    if (self.in_pure_ctx != self.is_pure(fun, func_did))
                        && !is_overloaded_item(self.tcx, func_did)
                    {
                        let msg = if self.in_pure_ctx {
                            "called impure program function in logical context"
                        } else {
                            "called logical function in impure context"
                        };

                        self.tcx.sess.span_err_with_code(
                            self.thir[fun].span,
                            format!("{} {:?}", msg, self.tcx.def_path_str(func_did)),
                            rustc_errors::DiagnosticId::Error(String::from("creusot")),
                        );
                    }
                } else if self.in_pure_ctx {
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
