use super::pearlite::{normalize, Literal, Term, TermKind};
use crate::{ctx::*, util};
use rustc_ast::{
    ast::{AttrArgs, AttrArgsEq},
    AttrItem,
};
use rustc_hir::def_id::DefId;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::{self, Body, Local, SourceInfo, SourceScope, OUTERMOST_SOURCE_SCOPE},
    ty::{EarlyBinder, GenericArgs, GenericArgsRef, ParamEnv, TyCtxt},
};
use rustc_span::Symbol;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, Default, TypeFoldable, TypeVisitable)]
pub struct PreContract<'tcx> {
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) requires: Vec<Term<'tcx>>,
    pub(crate) ensures: Vec<Term<'tcx>>,
    pub(crate) no_panic: bool,
    pub(crate) terminates: bool,
    pub(crate) extern_no_spec: bool,
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

    pub(crate) fn is_requires_false(&self) -> bool {
        self.requires.iter().any(|req| matches!(req.kind, TermKind::Lit(Literal::Bool(false))))
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
    pub(crate) no_panic: bool,
    pub(crate) terminates: bool,
}

impl ContractClauses {
    pub(crate) fn new() -> Self {
        Self {
            variant: None,
            requires: Vec::new(),
            ensures: Vec::new(),
            no_panic: false,
            terminates: false,
        }
    }

    fn get_pre<'tcx>(self, ctx: &mut TranslationCtx<'tcx>) -> EarlyBinder<'tcx, PreContract<'tcx>> {
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
        log::trace!("no_panic: {}", self.no_panic);
        out.no_panic = self.no_panic;
        log::trace!("terminates: {}", self.terminates);
        out.terminates = self.terminates;
        EarlyBinder::bind(out)
    }

    pub(crate) fn iter_ids(&self) -> impl Iterator<Item = DefId> + '_ {
        self.requires.iter().chain(self.ensures.iter()).chain(self.variant.iter()).cloned()
    }
}

#[derive(Debug)]
struct ScopeTree<'tcx>(
    HashMap<SourceScope, (HashSet<(Symbol, mir::Place<'tcx>)>, Option<SourceScope>)>,
);

impl<'tcx> ScopeTree<'tcx> {
    fn build(body: &Body<'tcx>) -> Self {
        use rustc_middle::mir::VarDebugInfoContents::Place;
        let mut scope_tree: HashMap<SourceScope, (HashSet<_>, Option<_>)> = Default::default();

        for var_info in &body.var_debug_info {
            // All variables in the DebugVarInfo should be user variables and thus be just locals
            let p = match var_info.value {
                Place(p) => p,
                _ => continue,
            };
            let info = var_info.source_info;

            let scope = info.scope;
            let scope_data = &body.source_scopes[scope];

            let entry = scope_tree.entry(scope).or_default();

            let name = var_info.name;
            entry.0.insert((name, p));

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

    fn visible_locals(&self, scope: SourceScope) -> HashMap<Symbol, mir::Place<'tcx>> {
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
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    locals: &HashMap<Local, Symbol>,
    info: SourceInfo,
) -> HashMap<Symbol, Term<'tcx>> {
    let mut args = HashMap::new();

    let tree = ScopeTree::build(body);

    for (k, p) in tree.visible_locals(info.scope) {
        args.insert(k, place_to_term(tcx, p, locals, body));
    }

    args
}

fn place_to_term<'tcx>(
    tcx: TyCtxt<'tcx>,
    p: mir::Place<'tcx>,
    locals: &HashMap<Local, Symbol>,
    body: &Body<'tcx>,
) -> Term<'tcx> {
    let ty = p.ty(&body.local_decls, tcx).ty;
    let span = body.local_decls[p.local].source_info.span;
    let mut kind = TermKind::Var(locals[&p.local]);
    for (place_ref, proj) in p.iter_projections() {
        let ty = place_ref.ty(&body.local_decls, tcx).ty;
        let term = Term { ty, span, kind };
        kind = match proj {
            mir::ProjectionElem::Deref => TermKind::Cur { term: Box::new(term) },
            mir::ProjectionElem::Field(field_idx, _) => {
                TermKind::Projection { lhs: Box::new(term), name: field_idx }
            }
            mir::ProjectionElem::Index(_) => todo!("make this work!"),
            mir::ProjectionElem::ConstantIndex { .. }
            | mir::ProjectionElem::Subslice { .. }
            | mir::ProjectionElem::OpaqueCast(_)
            | mir::ProjectionElem::Subtype(_) => {
                unimplemented!("projection {:?} is not supported in logic", proj)
            }
            mir::ProjectionElem::Downcast(..) => term.kind,
        };
    }
    Term { ty, span, kind }
}

#[derive(Debug)]
#[allow(dead_code)]
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

        if attributes_matches(attr, &["creusot", "clause", "requires"]) {
            contract.requires.push(get_creusot_item()?)
        } else if attributes_matches(attr, &["creusot", "clause", "ensures"]) {
            contract.ensures.push(get_creusot_item()?);
        } else if attributes_matches(attr, &["creusot", "clause", "variant"]) {
            contract.variant = Some(get_creusot_item()?);
        } else if attributes_matches(attr, &["creusot", "clause", "terminates"]) {
            contract.terminates = true;
        } else if attributes_matches(attr, &["creusot", "clause", "no_panic"]) {
            contract.no_panic = true;
        }
    }

    Ok(contract)
}

fn attributes_matches(attr: &AttrItem, to_match: &[&str]) -> bool {
    let segments = &attr.path.segments;
    if segments.len() < to_match.len() {
        return false;
    }
    for (segment, &to_match) in std::iter::zip(segments, to_match) {
        if segment.ident.as_str() != to_match {
            return false;
        }
    }
    true
}

pub(crate) fn inherited_extern_spec<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    let subst = GenericArgs::identity_for_item(ctx.tcx, def_id);
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
        (id, trait_ref.instantiate(ctx.tcx, subst).args)
    }
}

pub(crate) fn contract_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> PreContract<'tcx> {
    if let Some(extern_spec) = ctx.extern_spec(def_id).cloned() {
        let mut contract =
            extern_spec.contract.get_pre(ctx).instantiate(ctx.tcx, extern_spec.subst);
        contract.subst(&extern_spec.arg_subst.iter().cloned().collect());
        contract.normalize(ctx.tcx, ctx.param_env(def_id))
    } else if let Some((parent_id, subst)) = inherited_extern_spec(ctx, def_id) {
        let spec = ctx.extern_spec(parent_id).cloned().unwrap();
        let mut contract = spec.contract.get_pre(ctx).instantiate(ctx.tcx, subst);
        contract.subst(&spec.arg_subst.iter().cloned().collect());
        contract.normalize(ctx.tcx, ctx.param_env(def_id))
    } else {
        let subst = GenericArgs::identity_for_item(ctx.tcx, def_id);
        let mut contract =
            contract_clauses_of(ctx, def_id).unwrap().get_pre(ctx).instantiate(ctx.tcx, subst);

        if contract.is_empty()
            && !def_id.is_local()
            && ctx.externs.get(def_id.krate).is_none()
            && util::item_type(ctx.tcx, def_id) == ItemType::Program
        {
            contract.extern_no_spec = true;
            contract.requires.push(Term::mk_false(ctx.tcx));
        }

        contract
    }
}
