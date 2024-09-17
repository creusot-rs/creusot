use crate::{
    backend::ty_inv::TyInvKind,
    ctx::*,
    translation::{
        pearlite::{self, super_visit_mut_term, Term, TermKind, TermVisitorMut},
        specification::PreContract,
    },
};
use indexmap::IndexMap;
use itertools::izip;
use rustc_ast::{
    ast::{AttrArgs, AttrArgsEq},
    visit::{walk_fn, FnKind, Visitor},
    AttrItem, AttrKind, Attribute, FnSig, NodeId,
};
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
    Safety,
};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{
    self, BorrowKind, ClosureKind, EarlyBinder, GenericArg, GenericArgs, GenericArgsRef,
    ResolverAstLowering, Ty, TyCtxt, TyKind, UpvarCapture,
};
use rustc_span::{symbol, symbol::kw, Span, Symbol, DUMMY_SP};
use std::{
    collections::{HashMap, HashSet},
    fmt::{Display, Formatter},
    iter,
};
use why3::{
    declaration,
    declaration::{LetKind, Signature, ValDecl},
    Ident,
};

pub(crate) fn no_mir(tcx: TyCtxt, def_id: DefId) -> bool {
    is_no_translate(tcx, def_id) || is_predicate(tcx, def_id) || is_logic(tcx, def_id)
}

pub(crate) fn is_pearlite(tcx: TyCtxt, def_id: DefId) -> bool {
    is_predicate(tcx, def_id)
        || is_spec(tcx, def_id)
        || is_logic(tcx, def_id)
        || is_assertion(tcx, def_id)
        || is_snapshot_closure(tcx, def_id)
}

pub(crate) fn is_no_translate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "no_translate"]).is_some()
}

pub(crate) fn is_spec(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec"]).is_some()
}

pub(crate) fn is_invariant(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "invariant"]).is_some()
}

pub(crate) fn is_loop_variant(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "variant", "loop_"]).is_some()
}

pub(crate) fn is_variant(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "variant"]).is_some()
}

pub(crate) fn is_assertion(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "assert"]).is_some()
}

pub(crate) fn is_snapshot_closure(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "snapshot"]).is_some()
}

pub(crate) fn is_ghost_closure(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "ghost"]).is_some()
}

pub(crate) fn snapshot_closure_id<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<DefId> {
    if let TyKind::Closure(def_id, _) = ty.peel_refs().kind() {
        if is_snapshot_closure(tcx, *def_id) {
            return Some(*def_id);
        }
    }
    None
}

pub(crate) fn is_snap_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let r: Option<bool> = try {
        let adt = ty.ty_adt_def()?;
        let builtin = get_builtin(tcx, adt.did())?;
        builtin.as_str() == "prelude.prelude.Snapshot.snap_ty"
    };
    r.unwrap_or(false)
}

pub(crate) fn is_logic(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "logic"]).is_some()
}

pub(crate) fn is_prophetic(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "logic", "prophetic"]).is_some()
}

pub(crate) fn is_predicate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "predicate"]).is_some()
}

pub(crate) fn is_trusted(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "trusted"]).is_some()
}

pub(crate) fn is_law(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "law"]).is_some()
}

pub(crate) fn should_replace_trigger(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "no_trigger"]).is_none()
}

pub(crate) fn is_extern_spec(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "extern_spec"]).is_some()
}

pub(crate) fn is_ignore_structural_inv(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "trusted_ignore_structural_inv"]).is_some()
}

pub(crate) fn has_variant_clause(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "clause", "variant"]).is_some()
}

pub(crate) fn is_open_inv_result(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "open_inv_result"]).is_some()
}

pub(crate) fn is_inv_internal(tcx: TyCtxt, def_id: DefId) -> bool {
    tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap() == def_id
}

pub(crate) fn opacity_witness_name(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "clause", "open"]).and_then(|item| {
        match &item.args {
            AttrArgs::Eq(_, AttrArgsEq::Hir(l)) => Some(l.symbol),
            _ => None,
        }
    })
}

pub(crate) fn why3_attrs(tcx: TyCtxt, def_id: DefId) -> Vec<why3::declaration::Attribute> {
    let matches = get_attrs(tcx.get_attrs_unchecked(def_id), &["why3", "attr"]);
    matches
        .into_iter()
        .map(|a| declaration::Attribute::Attr(a.value_str().unwrap().as_str().into()))
        .collect()
}

pub(crate) fn param_def_id(tcx: TyCtxt, def_id: LocalDefId) -> LocalDefId {
    if is_spec(tcx, def_id.to_def_id()) && tcx.is_closure_like(def_id.to_def_id()) {
        tcx.parent(def_id.to_def_id()).expect_local()
    } else {
        def_id
    }
}

pub(crate) fn should_translate(tcx: TyCtxt, mut def_id: DefId) -> bool {
    loop {
        if is_no_translate(tcx, def_id) {
            return false;
        }

        if tcx.is_closure_like(def_id) {
            def_id = tcx.parent(def_id);
        } else {
            return true;
        }
    }
}

pub(crate) fn has_body(ctx: &mut TranslationCtx, def_id: DefId) -> bool {
    if let Some(local_id) = def_id.as_local() {
        ctx.tcx.hir().maybe_body_owned_by(local_id).is_some()
    } else {
        match item_type(ctx.tcx, def_id) {
            ItemType::Logic { .. } | ItemType::Predicate { .. } => ctx.term(def_id).is_some(),
            _ => false,
        }
    }
}

pub(crate) fn get_builtin(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "builtins"]).and_then(|a| {
        match &a.args {
            AttrArgs::Eq(_, AttrArgsEq::Hir(l)) => Some(l.symbol),
            _ => None,
        }
    })
}

pub(crate) fn item_name(tcx: TyCtxt, def_id: DefId, ns: Namespace) -> Ident {
    item_symb(tcx, def_id, ns).to_string().into()
}

pub(crate) fn item_symb(tcx: TyCtxt, def_id: DefId, ns: Namespace) -> Symbol {
    use rustc_hir::def::DefKind::*;

    match tcx.def_kind(def_id) {
        AssocTy => tcx.item_name(def_id),
        Ctor(_, _) => Symbol::intern(&format!("C_{}", tcx.item_name(def_id))),
        Struct | Variant | Union if ns == Namespace::ValueNS => {
            Symbol::intern(&format!("C_{}", tcx.item_name(def_id)))
        }
        Variant | Struct | Enum | Union => {
            Symbol::intern(&format!("t_{}", tcx.item_name(def_id).as_str().to_ascii_lowercase()))
        }
        Closure => {
            let mut id = ident_path(tcx, def_id).to_string();
            id = id.to_ascii_lowercase().into();
            Symbol::intern(&id)
        }

        _ => tcx.item_name(def_id),
    }
}

pub(crate) fn ident_of(sym: Symbol) -> Ident {
    let mut id = sym.to_string();

    id[..1].make_ascii_lowercase();

    if sym.as_str() == id {
        Ident::build(&id)
    } else {
        id += &"'";
        Ident::build(&id)
    }
}

pub(crate) fn inv_module_name(tcx: TyCtxt, kind: TyInvKind) -> Ident {
    match kind {
        TyInvKind::NotStructural => "TyInv_NotStructural".into(),
        TyInvKind::Trivial => "TyInv_Trivial".into(),
        TyInvKind::Adt(adt_did) => format!("{}_Inv", ident_path(tcx, adt_did)).into(),
        TyInvKind::Tuple(arity) => format!("TyInv_Tuple{arity}").into(),
    }
}

pub(crate) fn module_name(tcx: TyCtxt, def_id: DefId) -> Symbol {
    let kind = tcx.def_kind(def_id);
    use rustc_hir::def::DefKind::*;

    match kind {
        Ctor(_, _) | Variant => module_name(tcx, tcx.parent(def_id)),
        _ => ident_path(tcx, def_id),
    }
}

pub(crate) fn ident_path(tcx: TyCtxt, def_id: DefId) -> Symbol {
    use heck::ToUpperCamelCase;

    let def_path = tcx.def_path(def_id);

    let mut segments = Vec::new();

    let mut crate_name = tcx.crate_name(def_id.krate).to_string().to_upper_camel_case();
    if crate_name.chars().next().unwrap().is_numeric() {
        crate_name = format!("C{}", crate_name);
    }

    segments.push(crate_name);

    for seg in def_path.data[..].iter() {
        match seg.data {
            _ => segments.push(format!("{}", seg).to_upper_camel_case()),
        }
    }

    if let Some(Namespace::TypeNS) = tcx.def_kind(def_id).ns() {
        segments.push("Type".into());
    }

    Symbol::intern(&segments.join("_"))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemType {
    Logic { prophetic: bool },
    Predicate { prophetic: bool },
    Program,
    Closure,
    Trait,
    Impl,
    Type,
    AssocTy,
    Constant,
    Variant,
    Unsupported(DefKind),
    Field,
}

impl ItemType {
    pub(crate) fn let_kind(&self) -> Option<LetKind> {
        match self {
            ItemType::Logic { .. } => Some(LetKind::Function),
            ItemType::Predicate { .. } => Some(LetKind::Predicate),
            ItemType::Program | ItemType::Closure => None,
            ItemType::Constant => Some(LetKind::Constant),
            _ => None,
        }
    }

    pub(crate) fn val(&self, mut sig: Signature) -> ValDecl {
        match self {
            ItemType::Logic { .. } => {
                ValDecl { sig, ghost: false, val: false, kind: Some(LetKind::Function) }
            }
            ItemType::Predicate { .. } => {
                sig.retty = None;
                ValDecl { sig, ghost: false, val: false, kind: Some(LetKind::Predicate) }
            }
            ItemType::Program | ItemType::Closure => {
                ValDecl { sig, ghost: false, val: true, kind: None }
            }
            ItemType::Constant => {
                ValDecl { sig, ghost: false, val: true, kind: Some(LetKind::Constant) }
            }
            _ => unreachable!(),
        }
    }

    pub(crate) fn to_str(&self) -> &str {
        match self {
            ItemType::Logic { prophetic: false } => "logic function",
            ItemType::Logic { prophetic: true } => "prophetic logic function",
            ItemType::Predicate { prophetic: false } => "predicate",
            ItemType::Predicate { prophetic: true } => "prophetic predicate",
            ItemType::Program => "program function",
            ItemType::Closure => "closure",
            ItemType::Trait => "trait declaration",
            ItemType::Impl => "trait implementation",
            ItemType::Type => "type declaration",
            ItemType::AssocTy => "associated type",
            ItemType::Constant => "constant",
            ItemType::Field => "field",
            ItemType::Unsupported(_) => "[OTHER]",
            ItemType::Variant => "constructor",
        }
    }

    pub(crate) fn can_implement(self, trait_type: Self) -> bool {
        match (self, trait_type) {
            (ItemType::Logic { prophetic: false }, ItemType::Logic { prophetic: true }) => true,
            (ItemType::Predicate { prophetic: false }, ItemType::Predicate { prophetic: true }) => {
                true
            }
            _ => self == trait_type,
        }
    }
}

pub(crate) fn item_type(tcx: TyCtxt<'_>, def_id: DefId) -> ItemType {
    match tcx.def_kind(def_id) {
        DefKind::Trait => ItemType::Trait,
        DefKind::Impl { .. } => ItemType::Impl,
        DefKind::Fn | DefKind::AssocFn => {
            if is_predicate(tcx, def_id) {
                ItemType::Predicate { prophetic: is_prophetic(tcx, def_id) }
            } else if is_logic(tcx, def_id) {
                ItemType::Logic { prophetic: is_prophetic(tcx, def_id) }
            } else {
                ItemType::Program
            }
        }
        DefKind::AssocConst | DefKind::Const => ItemType::Constant,
        DefKind::Closure => ItemType::Closure,
        DefKind::Struct | DefKind::Enum | DefKind::Union => ItemType::Type,
        DefKind::AssocTy => ItemType::AssocTy,
        DefKind::Field => ItemType::Field,
        DefKind::AnonConst => panic!(),
        DefKind::Variant => ItemType::Variant,
        dk => ItemType::Unsupported(dk),
    }
}

pub(crate) fn inputs_and_output<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> (impl Iterator<Item = (symbol::Ident, Ty<'tcx>)>, Ty<'tcx>) {
    let ty = tcx.type_of(def_id).instantiate_identity();
    let (inputs, output): (Box<dyn Iterator<Item = (rustc_span::symbol::Ident, _)>>, _) = match ty
        .kind()
    {
        TyKind::FnDef(..) => {
            let gen_sig = tcx.fn_sig(def_id).instantiate_identity();
            let sig = tcx.normalize_erasing_late_bound_regions(tcx.param_env(def_id), gen_sig);
            let iter = tcx.fn_arg_names(def_id).iter().cloned().zip(sig.inputs().iter().cloned());
            (Box::new(iter), sig.output())
        }
        TyKind::Closure(_, subst) => {
            let sig = tcx.signature_unclosure(subst.as_closure().sig(), Safety::Safe);
            let sig = tcx.normalize_erasing_late_bound_regions(tcx.param_env(def_id), sig);
            let env_ty = tcx.closure_env_ty(ty, subst.as_closure().kind(), tcx.lifetimes.re_erased);

            // I wish this could be called "self"
            let closure_env = (symbol::Ident::empty(), env_ty);
            let names = tcx
                .fn_arg_names(def_id)
                .iter()
                .cloned()
                .chain(iter::repeat(rustc_span::symbol::Ident::empty()));
            (
                Box::new(iter::once(closure_env).chain(names.zip(sig.inputs().iter().cloned()))),
                sig.output(),
            )
        }
        _ => (Box::new(iter::empty()), tcx.type_of(def_id).instantiate_identity()),
    };
    (inputs, output)
}

#[derive(TypeVisitable, TypeFoldable, Debug, Clone)]
pub struct PreSignature<'tcx> {
    pub(crate) inputs: Vec<(symbol::Symbol, Span, Ty<'tcx>)>,
    pub(crate) output: Ty<'tcx>,
    pub(crate) contract: PreContract<'tcx>,
    // trusted: bool,
    // span: Span,
    // program: bool,
}

impl<'tcx> PreSignature<'tcx> {
    pub(crate) fn normalize(mut self, tcx: TyCtxt<'tcx>, param_env: ty::ParamEnv<'tcx>) -> Self {
        self.contract = self.contract.normalize(tcx, param_env);
        self
    }
}

pub(crate) fn pre_sig_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> PreSignature<'tcx> {
    let (inputs, output) = inputs_and_output(ctx.tcx, def_id);

    let mut contract = crate::specification::contract_of(ctx, def_id);

    let fn_ty = ctx.tcx.type_of(def_id).instantiate_identity();

    if let TyKind::Closure(_, subst) = fn_ty.kind() {
        let self_ = Symbol::intern("_1");
        let mut pre_subst = closure_capture_subst(ctx.tcx, def_id, subst, None, self_);

        let mut s = HashMap::new();
        let kind = subst.as_closure().kind();

        let env_ty = ctx.closure_env_ty(fn_ty, kind, ctx.lifetimes.re_erased);
        s.insert(
            self_,
            if env_ty.is_ref() { Term::var(self_, env_ty).cur() } else { Term::var(self_, env_ty) },
        );
        for pre in &mut contract.requires {
            pre_subst.visit_mut_term(pre);

            pre.subst(&s);
        }

        if kind == ClosureKind::FnMut {
            let args = subst.as_closure().sig().inputs().skip_binder()[0];
            let unnest_subst =
                ctx.mk_args(&[GenericArg::from(args), GenericArg::from(env_ty.peel_refs())]);

            let unnest_id = ctx.get_diagnostic_item(Symbol::intern("fn_mut_impl_unnest")).unwrap();

            contract.ensures.push(Term::call(
                ctx.tcx,
                unnest_id,
                unnest_subst,
                vec![Term::var(self_, env_ty).cur(), Term::var(self_, env_ty).fin()],
            ));
        };

        let mut post_subst =
            closure_capture_subst(ctx.tcx, def_id, subst, Some(subst.as_closure().kind()), self_);
        for post in &mut contract.ensures {
            post_subst.visit_mut_term(post);
        }

        assert!(contract.variant.is_none());
    }

    let mut inputs: Vec<_> = inputs
        .enumerate()
        .map(|(idx, (ident, ty))| {
            if ident.name.as_str() == "result" {
                ctx.crash_and_error(ident.span, "`result` is not allowed as a parameter name")
            }

            let name = if ident.name.as_str().is_empty() {
                anonymous_param_symbol(idx)
            } else {
                ident.name
            };
            (name, ident.span, ty)
        })
        .collect();
    if ctx.type_of(def_id).instantiate_identity().is_fn() && inputs.is_empty() {
        inputs.push((kw::Empty, DUMMY_SP, ctx.tcx.types.unit));
    };

    let mut pre_sig = PreSignature { inputs, output, contract };
    elaborate_type_invariants(ctx, def_id, &mut pre_sig);
    pre_sig
}

fn elaborate_type_invariants<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    pre_sig: &mut PreSignature<'tcx>,
) {
    if is_pearlite(ctx.tcx, def_id) {
        return;
    }

    let subst = GenericArgs::identity_for_item(ctx.tcx, def_id);

    let params_open_inv: HashSet<usize> = ctx
        .params_open_inv(def_id)
        .iter()
        .copied()
        .flatten()
        .map(|&i| if ctx.tcx.is_closure_like(def_id) { i + 1 } else { i })
        .collect();
    for (i, (name, span, ty)) in pre_sig.inputs.iter().enumerate() {
        if params_open_inv.contains(&i) {
            continue;
        }
        if let Some(term) = pearlite::type_invariant_term(ctx, def_id, *name, *span, *ty) {
            let term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
            pre_sig.contract.requires.push(term);
        }
    }

    let ret_ty_span: Option<Span> = try { ctx.tcx.hir().get_fn_output(def_id.as_local()?)?.span() };
    if !is_open_inv_result(ctx.tcx, def_id)
        && let Some(term) = pearlite::type_invariant_term(
            ctx,
            def_id,
            Symbol::intern("result"),
            ret_ty_span.unwrap_or_else(|| ctx.tcx.def_span(def_id)),
            pre_sig.output,
        )
    {
        let term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
        pre_sig.contract.ensures.push(term);
    }
}

pub(crate) fn get_attr<'a>(attrs: &'a [Attribute], path: &[&str]) -> Option<&'a AttrItem> {
    for attr in attrs.iter() {
        if attr.is_doc_comment() {
            continue;
        }

        let attr = attr.get_normal_item();

        if attr.path.segments.len() != path.len() {
            continue;
        }

        let matches = attr
            .path
            .segments
            .iter()
            .zip(path.iter())
            .fold(true, |acc, (seg, s)| acc && &*seg.ident.as_str() == *s);

        if matches {
            return Some(attr);
        }
    }
    None
}

pub(crate) fn get_attrs<'a>(attrs: &'a [Attribute], path: &[&str]) -> Vec<&'a Attribute> {
    let mut matched = Vec::new();

    for attr in attrs.iter() {
        if attr.is_doc_comment() {
            continue;
        }

        let item = attr.get_normal_item();

        if item.path.segments.len() != path.len() {
            continue;
        }

        let matches = item
            .path
            .segments
            .iter()
            .zip(path.iter())
            .fold(true, |acc, (seg, s)| acc && &*seg.ident.as_str() == *s);

        if matches {
            matched.push(attr)
        }
    }
    matched
}

pub(crate) fn is_attr(attr: &Attribute, str: &str) -> bool {
    match &attr.kind {
        AttrKind::DocComment(..) => false,
        AttrKind::Normal(attr) => {
            let segments = &attr.item.path.segments;
            segments.len() >= 2
                && segments[0].ident.as_str() == "creusot"
                && segments[1].ident.as_str() == str
        }
    }
}

use rustc_span::def_id::LocalDefId;
use rustc_target::abi::FieldIdx;

// Responsible for replacing occurences of captured variables with projections from the closure environment.
// Must also account for the *kind* of capture and the *kind* of closure involved each time.
pub(crate) struct ClosureSubst<'tcx> {
    self_: Term<'tcx>,
    kind: Option<ClosureKind>,

    map: IndexMap<Symbol, (UpvarCapture, Ty<'tcx>, FieldIdx)>,
    bound: HashSet<Symbol>,
}

impl<'tcx> ClosureSubst<'tcx> {
    // TODO: Simplify this logic.
    fn var(&self, x: Symbol) -> Option<Term<'tcx>> {
        let (ck, ty, ix) = *self.map.get(&x)?;

        let self_ = match self.kind {
            None => self.self_.clone(),
            Some(ClosureKind::Fn) => self.self_.clone().cur(),
            Some(ClosureKind::FnMut) => self.self_.clone().fin(),
            Some(ClosureKind::FnOnce) => self.self_.clone(),
        };

        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self_), name: ix },
            span: DUMMY_SP,
        };

        match ck {
            UpvarCapture::ByValue => Some(proj),
            UpvarCapture::ByRef(BorrowKind::MutBorrow | BorrowKind::UniqueImmBorrow)
                if self.kind == Some(ClosureKind::FnOnce) =>
            {
                Some(proj.fin())
            }
            UpvarCapture::ByRef(_) => Some(proj.cur()),
        }
    }

    fn old(&self, x: Symbol) -> Option<Term<'tcx>> {
        let (ck, ty, ix) = *self.map.get(&x)?;

        let self_ = match self.kind {
            Some(ClosureKind::Fn) => self.self_.clone().cur(),
            Some(ClosureKind::FnMut) => self.self_.clone().cur(),
            Some(ClosureKind::FnOnce) => self.self_.clone(),
            None => unreachable!(),
        };

        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: Box::new(self_), name: ix },
            span: DUMMY_SP,
        };

        match ck {
            UpvarCapture::ByValue => Some(proj),
            UpvarCapture::ByRef(_) => Some(proj.cur()),
        }
    }
}

impl<'tcx> TermVisitorMut<'tcx> for ClosureSubst<'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        match &term.kind {
            TermKind::Old { term: box Term { kind: TermKind::Var(x), .. }, .. } => {
                if !self.bound.contains(&x) {
                    if let Some(v) = self.old(*x) {
                        *term = v;
                    }
                    return;
                }
            }
            TermKind::Var(x) => {
                if !self.bound.contains(&x) {
                    if let Some(v) = self.var(*x) {
                        *term = v;
                    }
                }
            }
            TermKind::Quant { binder, .. } => {
                let mut bound = self.bound.clone();
                for name in &binder.0 {
                    bound.insert(name.name);
                }
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Match { arms, .. } => {
                let mut bound = self.bound.clone();
                arms.iter().for_each(|arm| arm.0.binds(&mut bound));
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Let { pattern, .. } => {
                let mut bound = self.bound.clone();
                pattern.binds(&mut bound);
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Closure { .. } => {
                super_visit_mut_term(term, self);
            }
            _ => super_visit_mut_term(term, self),
        }
    }
}

pub(crate) fn closure_capture_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    cs: GenericArgsRef<'tcx>,
    // What kind of substitution we should generate. The same precondition can be used in several ways
    ck: Option<ty::ClosureKind>,
    self_name: Symbol,
) -> ClosureSubst<'tcx> {
    let mut fun_def_id = def_id;
    while tcx.is_closure_like(fun_def_id) {
        fun_def_id = tcx.parent(fun_def_id);
    }

    let captures = tcx.closure_captures(def_id.expect_local());

    let ty = match ck {
        Some(ClosureKind::Fn) => Ty::new_imm_ref(
            tcx,
            tcx.lifetimes.re_erased,
            tcx.type_of(def_id).instantiate_identity(),
        ),
        Some(ClosureKind::FnMut) => Ty::new_mut_ref(
            tcx,
            tcx.lifetimes.re_erased,
            tcx.type_of(def_id).instantiate_identity(),
        ),
        Some(ClosureKind::FnOnce) | None => tcx.type_of(def_id).instantiate_identity(),
    };

    let self_ = Term::var(self_name, ty);

    let subst = izip!(captures, cs.as_closure().upvar_tys())
        .enumerate()
        .map(|(ix, (cap, ty))| (cap.to_symbol(), (cap.info.capture_kind, ty, ix.into())))
        .collect();

    ClosureSubst { self_, kind: ck, map: subst, bound: Default::default() }
}

pub(crate) struct AnonymousParamName(pub(crate) usize);

impl Display for AnonymousParamName {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}", self.0 + 1)
    }
}

pub(crate) fn anonymous_param_symbol(idx: usize) -> Symbol {
    let name = format!("{}", AnonymousParamName(idx)); // Allocate on stack?
    Symbol::intern(&name)
}

pub(crate) fn gather_params_open_inv(tcx: TyCtxt) -> HashMap<DefId, Vec<usize>> {
    struct VisitFns<'a>(HashMap<DefId, Vec<usize>>, &'a ResolverAstLowering);
    impl<'a> Visitor<'a> for VisitFns<'a> {
        fn visit_fn(&mut self, fk: FnKind<'a>, _: Span, node: NodeId) {
            let decl = match fk {
                FnKind::Fn(_, _, FnSig { decl, .. }, _, _, _) => decl,
                FnKind::Closure(_, decl, _) => decl,
            };
            let mut open_inv_params = vec![];
            for (i, p) in decl.inputs.iter().enumerate() {
                if get_attr(&p.attrs, &["creusot", "open_inv"]).is_some() {
                    open_inv_params.push(i);
                }
            }
            let defid = self.1.node_id_to_def_id[&node].to_def_id();
            assert!(self.0.insert(defid, open_inv_params).is_none());
            walk_fn(self, fk)
        }
    }

    let (resolver, cr) = &*tcx.resolver_for_lowering().borrow();

    let mut visit = VisitFns(HashMap::new(), &resolver);
    visit.visit_crate(&*cr);
    visit.0
}
