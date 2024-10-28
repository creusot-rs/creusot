use crate::{
    contracts_items::{
        get_fn_mut_unnest, is_logic, is_no_translate, is_open_inv_result, is_pearlite,
        is_predicate, is_prophetic, is_snapshot_closure, is_spec,
    },
    ctx::*,
    translation::{
        pearlite::{self, super_visit_mut_term, Term, TermKind, TermVisitorMut},
        specification::PreContract,
    },
    very_stable_hash::get_very_stable_hash,
};
use indexmap::IndexMap;
use rustc_ast::{
    visit::{walk_fn, FnKind, Visitor},
    AttrItem, AttrKind, Attribute, FnSig, NodeId,
};
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
    definitions::{DefPathData, DisambiguatedDefPathData},
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
    path::PathBuf,
};
use why3::{
    declaration::{LetKind, Signature, ValDecl},
    Ident,
};

pub(crate) fn snapshot_closure_id<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<DefId> {
    if let TyKind::Closure(def_id, _) = ty.peel_refs().kind() {
        if is_snapshot_closure(tcx, *def_id) {
            return Some(*def_id);
        }
    }
    None
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

pub(crate) fn item_name(tcx: TyCtxt, def_id: DefId, ns: Namespace) -> Ident {
    item_symb(tcx, def_id, ns).to_string().into()
}

// Why3 value names must start with a lower case letter.
// Rust function names conventionally start with a lower case letter,
// but that is not mandatory, in which case we insert a prefix `v_`.
// To make this encoding injective, also insert `v_` if the source name already starts with an `v_`.
// This makes decoding simple: if the name starts with `v_`, just strip it.
pub fn value_name(name: &str) -> String {
    if name.starts_with(|c: char| c.is_ascii_lowercase()) && !name.starts_with("v_") {
        name.to_string()
    } else {
        format!("v_{}", name)
    }
}

pub fn type_name(name: &str) -> String {
    if name.starts_with(|c: char| c.is_ascii_lowercase()) && !name.starts_with("t_") {
        name.to_string()
    } else {
        format!("t_{}", name)
    }
}

pub fn translate_accessor_name(variant: &str, field: &str) -> String {
    format!("{}__{}", type_name(&translate_name(variant)), translate_name(field))
}

// The result should be a valid Why3 identifier.
pub(crate) fn item_symb(tcx: TyCtxt, def_id: DefId, ns: Namespace) -> Symbol {
    use rustc_hir::def::DefKind::*;

    match tcx.def_kind(def_id) {
        AssocTy => tcx.item_name(def_id), // TODO: is this used (the test suite passes if I replace this with panic!)?
        Ctor(_, _) => {
            Symbol::intern(&format!("C_{}", translate_name(tcx.item_name(def_id).as_str())))
        }
        Struct | Variant | Union if ns == Namespace::ValueNS => {
            Symbol::intern(&format!("C_{}", translate_name(tcx.item_name(def_id).as_str())))
        }
        Variant | Struct | Enum | Union => {
            Symbol::intern(&format!("t_{}", translate_name(tcx.item_name(def_id).as_str())))
        }
        Closure => lower_ident_path(tcx, def_id),
        _ => Symbol::intern(&value_name(&translate_name(tcx.item_name(def_id).as_str()))),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NS {
    T,
    M,
}

impl NS {
    pub fn as_str(&self) -> &str {
        match self {
            NS::T => "T",
            NS::M => "M",
        }
    }
}

/// Common representation of module name from which we can generate both
/// a Why3 module name (`M_krate__modl__f`) and a file name (`krate/modl/M_f.coma`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModulePath {
    path: Vec<Symbol>, // Crate and module names
    namespace: NS,     // "M" for functions, or "T" for types
    basename: Symbol,  // Function or type name
}

impl ModulePath {
    pub fn new(tcx: TyCtxt, def_id: DefId, namespace: NS) -> Self {
        let mut path: Vec<Symbol> = crate::util::ident_path_segments(tcx, def_id)
            .into_iter()
            .map(|s| Symbol::intern(&s))
            .collect();
        let basename = path.pop().unwrap();
        ModulePath { path, namespace, basename }
    }

    // `M_krate__modl__f`
    // Note: each fragment doesn't need to go through Ident (unlike why3_qname and file_name)
    pub fn why3_ident(&self) -> Ident {
        let mut path = self.namespace.as_str().to_string() + "_";
        for m in &self.path {
            path += m.as_str();
            path += "__";
        }
        path += self.basename.as_str();
        Ident::from_string(path)
    }

    // `krate.modl.M_f.Coma` (Coma is the toplevel name)
    // Note: pass each fragment through Ident::build() to filter out coma keywords.
    pub fn why3_qname(&self, prefix: &Vec<Ident>) -> why3::QName {
        let path = self.path.iter().map(|s| Ident::build(s.as_str())).chain(iter::once(
            Ident::build(&(self.namespace.as_str().to_string() + "_" + self.basename.as_str())),
        ));
        let module = prefix.into_iter().cloned().chain(path).collect::<Vec<_>>();
        let name = Ident::build("Coma");
        why3::QName { module, name }
    }

    /// Set `prefix` to `None` for monolithic output
    pub fn why3_name(&self, prefix: Option<&Vec<Ident>>) -> why3::QName {
        match prefix {
            Some(prefix) => self.why3_qname(prefix),
            None => why3::QName { module: vec![], name: self.why3_ident() },
        }
    }

    // `prefix/krate/modl/M_f.coma`
    // Note: pass each fragment through Ident::build() to filter out coma keywords
    // so that this produces the same names as `why3_qname()`.
    pub fn file_name(&self, prefix: &Vec<Ident>) -> PathBuf {
        let mut path = PathBuf::new();
        for m in prefix {
            path.push(m.as_str());
        }
        for m in &self.path {
            path.push(Ident::build(m.as_str()).as_str());
        }
        path.push(self.namespace.as_str().to_string() + "_" + &self.basename.as_str() + ".coma");
        path
    }
}

pub(crate) fn module_name(tcx: TyCtxt, def_id: DefId) -> Symbol {
    let kind = tcx.def_kind(def_id);
    use rustc_hir::def::DefKind::*;

    match kind {
        Ctor(_, _) | Variant => module_name(tcx, tcx.parent(def_id)),
        _ => upper_ident_path(tcx, def_id),
    }
}

// Translate a name to be a valid fragment of a Why3 identifier
// Escape initial and final underscores, double underscores, non-ascii characters,
// and "qy" sequences (because "qy" is the escape sequence).
// "qy123z" encodes the code point 123.
fn push_translate_name(n: &str, dest: &mut String) -> () {
    let mut chars = n.chars().peekable();
    // Escape initial underscore
    if chars.peek() == Some(&'_') {
        let _ = chars.next();
        dest.push_str("qy95z");
    }
    while let Some(c) = chars.next() {
        let is_qy = c == 'q' && chars.peek() == Some(&'y');
        if c == '_' {
            match chars.peek() {
                None | Some('_') => dest.push_str("qy95z"),
                _ => dest.push('_'),
            }
        } else if c.is_ascii_alphanumeric() && !is_qy {
            dest.push(c);
        } else {
            dest.push_str(&format!("qy{}z", c as u32));
        }
    }
}

pub fn translate_name(n: &str) -> String {
    let mut dest = String::new();
    push_translate_name(n, &mut dest);
    dest
}

enum Segment {
    Impl(u64), // Hash of the impl subject (type for inherent impl, trait+type for trait impls)
    Closure(u32), // Closure ID
    // There may be other variants than Impl and Closure to handle similarly.
    Other(DisambiguatedDefPathData),
}

fn ident_path_segments_(tcx: TyCtxt, def_id: DefId) -> Vec<Segment> {
    let mut segs = Vec::new();
    let mut id = def_id;
    loop {
        let key = tcx.def_key(id);
        let parent_id = match key.parent {
            None => break, // The last segment is CrateRoot. Skip it.
            Some(parent_id) => parent_id,
        };
        match key.disambiguated_data.data {
            DefPathData::Impl => {
                segs.push(Segment::Impl(get_very_stable_hash(&tcx.impl_subject(id), &tcx).as_u64()))
            }
            DefPathData::Closure => {
                segs.push(Segment::Closure(key.disambiguated_data.disambiguator))
            }
            _ => segs.push(Segment::Other(key.disambiguated_data)),
        }
        id.index = parent_id;
    }
    segs.reverse();
    segs
}

pub(crate) fn ident_path_segments(tcx: TyCtxt, def_id: DefId) -> Vec<String> {
    let krate = tcx.crate_name(def_id.krate);
    iter::once(translate_name(krate.as_str()))
        .chain(ident_path_segments_(tcx, def_id).into_iter().map(|seg| match seg {
            Segment::Impl(hash) => format!("qyi{}", hash),
            Segment::Closure(id) => format!("qyClosure{}", id),
            Segment::Other(data) => translate_name(&data.to_string()),
        }))
        .collect()
}

// This function must be injective: distinct source constructs
// must have different names in the output.
fn ident_path(upper_initial: bool, tcx: TyCtxt, def_id: DefId) -> Symbol {
    let mut dest = String::new();

    if let Some(Namespace::TypeNS) = tcx.def_kind(def_id).ns() {
        dest.push_str(if upper_initial { "T_" } else { "t_" });
    } else {
        dest.push_str(if upper_initial { "M_" } else { "m_" });
    }

    let crate_name = tcx.crate_name(def_id.krate);
    push_translate_name(crate_name.as_str(), &mut dest);

    let def_path = ident_path_segments_(tcx, def_id);
    for seg in def_path.iter() {
        dest.push_str("__");
        match seg {
            Segment::Impl(hash) => dest.push_str(&format!("qyi{}", hash)),
            Segment::Closure(id) => dest.push_str(&format!("qyClosure{}", id)),
            Segment::Other(data) => push_translate_name(&format!("{}", data), &mut dest),
        }
    }

    Symbol::intern(&dest)
}

// Coma module names must start with an upper case letter.
pub(crate) fn upper_ident_path(tcx: TyCtxt, def_id: DefId) -> Symbol {
    ident_path(true, tcx, def_id)
}

// Function and type names must start with a lower case letter.
pub(crate) fn lower_ident_path(tcx: TyCtxt, def_id: DefId) -> Symbol {
    ident_path(false, tcx, def_id)
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

            let unnest_id = get_fn_mut_unnest(ctx.tcx);

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

        let matches =
            attr.path.segments.iter().zip(path.iter()).all(|(seg, s)| &*seg.ident.as_str() == *s);

        if matches {
            return Some(attr);
        }
    }
    None
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

    let subst = std::iter::zip(captures, cs.as_closure().upvar_tys())
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
