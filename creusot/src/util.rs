use crate::{
    ctx::*,
    translation::{
        self,
        specification::{
            typing::{super_visit_mut_term, Literal, Term, TermKind, TermVisitorMut},
            PreContract,
        },
        ty::closure_accessor_name,
    },
};
use creusot_rustc::{
    ast::{
        ast::{MacArgs, MacArgsEq},
        AttrItem, AttrKind, Attribute,
    },
    hir::{def::DefKind, def_id::DefId, Unsafety},
    middle::ty::{
        self,
        subst::{InternalSubsts, SubstsRef},
        DefIdTree, EarlyBinder, ReErased, Subst, Ty, TyCtxt, TyKind, VariantDef,
    },
    resolve::Namespace,
    span::{symbol, Symbol, DUMMY_SP},
};
use indexmap::IndexMap;
use rustc_middle::ty::{ClosureKind, RegionKind};
use std::{
    collections::{HashMap, HashSet},
    iter,
};
use why3::{
    declaration,
    declaration::{Signature, ValKind},
    exp::{super_visit_mut, Binder, Constant, Exp, ExpMutVisitor},
    ty::Type,
    Ident, QName,
};

pub(crate) fn no_mir(tcx: TyCtxt, def_id: DefId) -> bool {
    crate::util::is_no_translate(tcx, def_id)
        || crate::util::is_logic(tcx, def_id)
        || crate::util::is_predicate(tcx, def_id)
}

pub(crate) fn is_no_translate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "no_translate"]).is_some()
}

pub(crate) fn is_spec(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "spec"]).is_some()
}

pub(crate) fn invariant_name(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "invariant"]).and_then(|a| {
        match &a.args {
            MacArgs::Eq(_, MacArgsEq::Hir(l)) => Some(l.token_lit.symbol),
            _ => None,
        }
    })
}

pub(crate) fn is_invariant(tcx: TyCtxt, def_id: DefId) -> bool {
    invariant_name(tcx, def_id).is_some()
}

pub(crate) fn is_assertion(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "assert"]).is_some()
}

pub(crate) fn is_ghost(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "spec", "ghost"]).is_some()
}

pub(crate) fn is_ghost_closure<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<DefId> {
    if let TyKind::Closure(def_id, _) = ty.peel_refs().kind()  && is_ghost(tcx, *def_id)  {
        Some(*def_id)
    } else { None }
}

pub(crate) fn is_predicate(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "predicate"]).is_some()
}

pub(crate) fn is_logic(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "logic"]).is_some()
}

pub(crate) fn is_trusted(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "trusted"]).is_some()
}

pub(crate) fn is_law(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "decl", "law"]).is_some()
}

pub(crate) fn is_extern_spec(tcx: TyCtxt, def_id: DefId) -> bool {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "extern_spec"]).is_some()
}

pub(crate) fn why3_attrs(tcx: TyCtxt, def_id: DefId) -> Vec<why3::declaration::Attribute> {
    let matches = get_attrs(tcx.get_attrs_unchecked(def_id), &["why3", "attr"]);
    matches
        .into_iter()
        .map(|a| declaration::Attribute::Attr(a.value_str().unwrap().as_str().into()))
        .collect()
}

pub(crate) fn closure_owner(tcx: TyCtxt, mut def_id: DefId) -> DefId {
    while tcx.is_closure(def_id) {
        def_id = tcx.parent(def_id);
    }

    def_id
}

pub(crate) fn should_translate(tcx: TyCtxt, mut def_id: DefId) -> bool {
    loop {
        if is_no_translate(tcx, def_id) {
            return false;
        }

        if tcx.is_closure(def_id) {
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
            ItemType::Logic | ItemType::Predicate => ctx.term(def_id).is_some(),
            _ => false,
        }
    }
}

pub(crate) fn get_builtin(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "builtins"]).and_then(|a| {
        match &a.args {
            MacArgs::Eq(_, MacArgsEq::Hir(l)) => Some(l.token_lit.symbol),
            _ => None,
        }
    })
}

pub(crate) fn constructor_qname(ctx: &TranslationCtx, var: &VariantDef) -> QName {
    QName {
        module: vec![module_name(ctx, var.def_id)],
        name: item_name(ctx.tcx, var.def_id, Namespace::ValueNS).to_string().into(),
    }
}

pub(crate) fn item_qname(ctx: &TranslationCtx, def_id: DefId, ns: Namespace) -> QName {
    QName { module: vec![module_name(ctx, def_id)], name: item_name(ctx.tcx, def_id, ns) }
}

pub(crate) fn item_name(tcx: TyCtxt, def_id: DefId, ns: Namespace) -> Ident {
    use creusot_rustc::hir::def::DefKind::*;

    match tcx.def_kind(def_id) {
        AssocTy => ident_of_ty(tcx.item_name(def_id)),
        Ctor(_, _) => format!("C_{}", tcx.item_name(def_id)).into(),
        Struct | Variant | Union if ns == Namespace::ValueNS => {
            format!("C_{}", tcx.item_name(def_id)).into()
        }
        Variant | Struct | Enum | Union => {
            format!("t_{}", tcx.item_name(def_id).as_str().to_ascii_lowercase()).into()
        }
        Closure => {
            let mut id = ident_path(tcx, def_id);
            if ns == Namespace::TypeNS {
                id = id.to_string().to_ascii_lowercase().into();
            } else {
                id.decapitalize();
            }
            id
        }

        _ => ident_of(tcx.item_name(def_id)),
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

pub(crate) fn ident_of_ty(sym: Symbol) -> Ident {
    let mut id = sym.to_string();

    id[..1].make_ascii_lowercase();
    Ident::build(&id)
}

pub(crate) fn module_name(ctx: &TranslationCtx, def_id: DefId) -> Ident {
    let kind = ctx.def_kind(def_id);
    use creusot_rustc::hir::def::DefKind::*;

    match kind {
        Ctor(_, _) | Variant => module_name(ctx, ctx.parent(def_id)),
        Struct | Enum => ident_path(ctx.tcx, ctx.representative_type(def_id)),
        _ => ident_path(ctx.tcx, def_id),
    }
}

fn ident_path(tcx: TyCtxt, def_id: DefId) -> Ident {
    use heck::CamelCase;

    let def_path = tcx.def_path(def_id);

    let mut segments = Vec::new();

    let mut crate_name = tcx.crate_name(def_id.krate).to_string().to_camel_case();
    if crate_name.chars().next().unwrap().is_numeric() {
        crate_name = format!("C{}", crate_name);
    }

    segments.push(crate_name);

    for seg in def_path.data[..].iter() {
        match seg.data {
            _ => segments.push(format!("{}", seg).to_camel_case()),
        }
    }

    if let Some(Namespace::TypeNS) = tcx.def_kind(def_id).ns() {
        segments.push("Type".into());
    }

    segments.join("_").into()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemType {
    Logic,
    Predicate,
    Program,
    Closure,
    Trait,
    Impl,
    Type,
    AssocTy,
    Constant,
    Unsupported(DefKind),
}

impl ItemType {
    pub(crate) fn val(&self, sig: Signature) -> ValKind {
        match self {
            ItemType::Logic => ValKind::Function { sig },
            ItemType::Predicate => ValKind::Predicate { sig },
            ItemType::Program => ValKind::Val { sig },
            _ => unreachable!(),
        }
    }

    pub(crate) fn to_str(&self) -> &str {
        match self {
            ItemType::Logic => "logic function",
            ItemType::Predicate => "predicate",
            ItemType::Program => "program function",
            ItemType::Closure => "closure",
            ItemType::Trait => "trait declaration",
            ItemType::Impl => "trait implementation",
            ItemType::Type => "type declaration",
            ItemType::AssocTy => "associated type",
            ItemType::Constant => "constant",
            ItemType::Unsupported(_) => "[OTHER]",
        }
    }
}

pub(crate) fn item_type(tcx: TyCtxt<'_>, def_id: DefId) -> ItemType {
    match tcx.def_kind(def_id) {
        DefKind::Trait => ItemType::Trait,
        DefKind::Impl => ItemType::Impl,
        DefKind::Fn | DefKind::AssocFn => {
            if is_predicate(tcx, def_id) {
                ItemType::Predicate
            } else if is_logic(tcx, def_id) {
                ItemType::Logic
            } else {
                ItemType::Program
            }
        }
        DefKind::AssocConst => ItemType::Constant,
        DefKind::Closure => ItemType::Closure,
        DefKind::Struct | DefKind::Enum | DefKind::Union => ItemType::Type,
        DefKind::AssocTy => ItemType::AssocTy,
        DefKind::AnonConst => panic!(),
        dk => ItemType::Unsupported(dk),
    }
}

pub(crate) fn inputs_and_output<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> (impl Iterator<Item = (creusot_rustc::span::symbol::Ident, Ty<'tcx>)>, Ty<'tcx>) {
    let (inputs, output): (Box<dyn Iterator<Item = (creusot_rustc::span::symbol::Ident, _)>>, _) =
        match tcx.type_of(def_id).kind() {
            TyKind::FnDef(..) => {
                let gen_sig = tcx.fn_sig(def_id);
                let sig = tcx.normalize_erasing_late_bound_regions(tcx.param_env(def_id), gen_sig);
                let iter =
                    tcx.fn_arg_names(def_id).iter().cloned().zip(sig.inputs().iter().cloned());
                (box iter, sig.output())
            }
            TyKind::Closure(_, subst) => {
                let sig = tcx.signature_unclosure(subst.as_closure().sig(), Unsafety::Normal);
                let sig = tcx.normalize_erasing_late_bound_regions(tcx.param_env(def_id), sig);
                let env_region = ReErased;
                let env_ty = tcx.closure_env_ty(def_id, subst, env_region).unwrap();

                let closure_env = (creusot_rustc::span::symbol::Ident::empty(), env_ty);
                let names = tcx
                    .fn_arg_names(def_id)
                    .iter()
                    .cloned()
                    .chain(iter::repeat(creusot_rustc::span::symbol::Ident::empty()));
                (
                    box iter::once(closure_env).chain(names.zip(sig.inputs().iter().cloned())),
                    sig.output(),
                )
            }
            _ => unreachable!(),
        };
    (inputs, output)
}

pub struct PreSignature<'tcx> {
    pub(crate) inputs: Vec<(symbol::Ident, Ty<'tcx>)>,
    pub(crate) output: Ty<'tcx>,
    pub(crate) contract: PreContract<'tcx>,
    // trusted: bool,
    // span: Span,
    // program: bool,
}

pub(crate) fn pre_sig_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> PreSignature<'tcx> {
    let (inputs, output) = inputs_and_output(ctx.tcx, def_id);

    let mut contract = crate::specification::contract_of(ctx, def_id);
    if output.is_never() {
        contract.ensures.push(Term {
            kind: TermKind::Lit(Literal::Bool(false)),
            ty: ctx.mk_ty(TyKind::Bool),
            span: DUMMY_SP,
        });
    }

    if let TyKind::Closure(_, subst) = ctx.tcx.type_of(def_id).kind() {
        let mut pre_subst =
            closure_capture_subst(ctx.tcx, def_id, subst, subst.as_closure().kind(), false);
        for pre in &mut contract.requires {
            pre_subst.visit_mut_term(pre);
        }

        let mut post_subst =
            closure_capture_subst(ctx.tcx, def_id, subst, subst.as_closure().kind(), true);
        for post in &mut contract.ensures {
            post_subst.visit_mut_term(post);
        }

        assert!(contract.variant.is_none());
    }

    PreSignature { inputs: inputs.collect(), output, contract }
}

pub(crate) fn signature_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
) -> Signature {
    debug!("signature_of {def_id:?}");
    let pre_sig = pre_sig_of(ctx, def_id);

    let contract = names.with_public_clones(|names| pre_sig.contract.to_exp(ctx, names, def_id));

    let name = item_name(ctx.tcx, def_id, Namespace::ValueNS);

    let span = ctx.tcx.def_span(def_id);
    let mut args: Vec<Binder> = names.with_public_clones(|names| {
        pre_sig
            .inputs
            .into_iter()
            .enumerate()
            .map(|(ix, (id, ty))| {
                let ty = translation::ty::translate_ty(ctx, names, span, ty);
                let id = if id.name.is_empty() {
                    format!("_{}'", ix + 1).into()
                } else if id.name == Symbol::intern("result") {
                    ctx.crash_and_error(id.span, "`result` is not allowed as a parameter name");
                } else {
                    ident_of(id.name)
                };
                Binder::typed(id, ty)
            })
            .collect()
    });

    if args.is_empty() {
        args.push(Binder::wild(Type::UNIT));
    };

    let mut attrs = why3_attrs(ctx.tcx, def_id);
    if matches!(item_type(ctx.tcx, def_id), ItemType::Program | ItemType::Closure) {
        attrs.push(declaration::Attribute::Attr("cfg:stackify".into()))
    };

    let retty = names.with_public_clones(|names| {
        translation::ty::translate_ty(ctx, names, span, pre_sig.output)
    });
    Signature { name, attrs, retty: Some(retty), args, contract }
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

use creusot_rustc::smir::mir::Field;

pub(crate) struct ClosureSubst<'tcx> {
    def_id: DefId,
    post: bool,
    self_: Term<'tcx>,
    map: IndexMap<Symbol, (Ty<'tcx>, Field)>,
    bound: HashSet<Symbol>,
}

impl<'tcx> ClosureSubst<'tcx> {
    fn var(&self, x: Symbol) -> Term<'tcx> {
        let (ty, ix) = *self.map.get(&x).unwrap_or_else(|| panic!("{:?} not found", x));

        let self_ = if self.self_.ty.is_ref() && self.self_.ty.is_mutable_ptr() {
            Term {
                ty: self.self_.ty.peel_refs(),
                kind: if self.post {
                    TermKind::Fin { term: box self.self_.clone() }
                } else {
                    TermKind::Cur { term: box self.self_.clone() }
                },
                span: DUMMY_SP,
            }
        } else {
            self.self_.clone()
        };
        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: box self_, name: ix, def: self.def_id },
            span: DUMMY_SP,
        };

        if ty.is_mutable_ptr() {
            Term { ty: ty.peel_refs(), kind: TermKind::Cur { term: box proj }, span: DUMMY_SP }
        } else {
            proj
        }
    }

    fn old(&self, x: Symbol) -> Term<'tcx> {
        let (ty, ix) = *self.map.get(&x).unwrap_or_else(|| panic!("{:?} not found", x));

        let self_ = if self.self_.ty.is_ref() && self.self_.ty.is_mutable_ptr() {
            Term {
                ty: self.self_.ty.peel_refs(),
                kind: TermKind::Cur { term: box self.self_.clone() },
                span: DUMMY_SP,
            }
        } else {
            self.self_.clone()
        };
        let proj = Term {
            ty,
            kind: TermKind::Projection { lhs: box self_, name: ix, def: self.def_id },
            span: DUMMY_SP,
        };

        if ty.is_mutable_ptr() {
            Term { ty: ty.peel_refs(), kind: TermKind::Cur { term: box proj }, span: DUMMY_SP }
        } else {
            proj
        }
    }
}

impl<'tcx> TermVisitorMut<'tcx> for ClosureSubst<'tcx> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        match &term.kind {
            TermKind::Old { term: box Term { kind: TermKind::Var(x), .. }, .. } => {
                if !self.bound.contains(&x) {
                    *term = self.old(*x);
                    return;
                }
            }
            TermKind::Var(x) => {
                if !self.bound.contains(&x) {
                    *term = self.var(*x);
                }
            }
            TermKind::Forall { binder, .. } => {
                let mut bound = self.bound.clone();
                bound.insert(binder.0);
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Exists { binder, .. } => {
                let mut bound = self.bound.clone();
                bound.insert(binder.0);
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
            TermKind::Closure { args, .. } => {
                let mut bound = self.bound.clone();
                args.iter().for_each(|a| a.binds(&mut bound));
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            _ => super_visit_mut_term(term, self),
        }
    }
}

pub(crate) fn closure_capture_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    cs: SubstsRef<'tcx>,
    // What kind of substitution we should generate. The same precondition can be used in several ways
    ck: ty::ClosureKind,
    is_post: bool,
) -> ClosureSubst {
    let mut fun_def_id = def_id;
    while tcx.is_closure(fun_def_id) {
        fun_def_id = tcx.parent(fun_def_id);
    }

    let capture_names =
        tcx.symbols_for_closure_captures((fun_def_id.expect_local(), def_id.expect_local()));
    let captures = capture_names.iter().zip(cs.as_closure().upvar_tys());

    let ty = match ck {
        ClosureKind::Fn => tcx.mk_imm_ref(tcx.mk_region(RegionKind::ReErased), tcx.type_of(def_id)),
        ClosureKind::FnMut => {
            tcx.mk_mut_ref(tcx.mk_region(RegionKind::ReErased), tcx.type_of(def_id))
        }
        ClosureKind::FnOnce => tcx.type_of(def_id),
    };

    let self_ = Term { ty, kind: TermKind::Var(Symbol::intern("_1'")), span: DUMMY_SP };

    let subst =
        captures.into_iter().enumerate().map(|(ix, (nm, ty))| (*nm, (ty, ix.into()))).collect();
    ClosureSubst { self_, map: subst, post: is_post, def_id, bound: Default::default() }
}
