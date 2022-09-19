use crate::{
    ctx::*,
    translation::{self, ty::closure_accessor_name},
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
    span::Symbol,
};
use std::{collections::HashMap, iter};
use why3::{
    declaration,
    declaration::{Signature, ValKind},
    exp::{super_visit_mut, Binder, Constant, Exp, ExpMutVisitor},
    ty::Type,
    Ident, QName,
};

pub fn parent_module(tcx: TyCtxt, def_id: DefId) -> DefId {
    let mut module_id = def_id;

    loop {
        module_id = tcx.parent(module_id);
        if tcx.def_kind(module_id) == DefKind::Mod {
            break;
        }
    }
    module_id
}

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

pub fn get_builtin(tcx: TyCtxt, def_id: DefId) -> Option<Symbol> {
    get_attr(tcx.get_attrs_unchecked(def_id), &["creusot", "builtins"]).and_then(|a| {
        match &a.args {
            MacArgs::Eq(_, MacArgsEq::Hir(l)) => Some(l.token_lit.symbol),
            _ => None,
        }
    })
}

pub fn constructor_qname(ctx: &TranslationCtx, var: &VariantDef) -> QName {
    QName {
        module: vec![module_name(ctx, var.def_id)],
        name: item_name(ctx.tcx, var.def_id, Namespace::ValueNS).to_string().into(),
    }
}

pub fn item_qname(ctx: &TranslationCtx, def_id: DefId, ns: Namespace) -> QName {
    QName { module: vec![module_name(ctx, def_id)], name: item_name(ctx.tcx, def_id, ns) }
}

pub fn item_name(tcx: TyCtxt, def_id: DefId, ns: Namespace) -> Ident {
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

pub fn module_name(ctx: &TranslationCtx, def_id: DefId) -> Ident {
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
    Interface,
    Constant,
    Unsupported(DefKind),
}

impl ItemType {
    // Whether this definition should be 'transparent' which affects
    // how we clone it. Transparent definitions will clone the *interface*
    // of their dependencies, even in their body module. In particular
    // this is used to get around the generativity of why3 clones for logic
    // functions.
    pub fn is_transparent(&self) -> bool {
        use ItemType::*;
        matches!(self, Logic | Predicate | Type | Interface)
    }

    pub fn logical(&self) -> bool {
        use ItemType::*;
        matches!(self, Logic | Predicate)
    }

    pub fn val(&self, sig: Signature) -> ValKind {
        match self {
            ItemType::Logic => ValKind::Function { sig },
            ItemType::Predicate => ValKind::Predicate { sig },
            ItemType::Program => ValKind::Val { sig },
            _ => unreachable!(),
        }
    }

    pub fn to_str(&self) -> &str {
        match self {
            ItemType::Logic => "logic function",
            ItemType::Predicate => "predicate",
            ItemType::Program => "program function",
            ItemType::Closure => "closure",
            ItemType::Trait => "trait declaration",
            ItemType::Impl => "trait implementation",
            ItemType::Type => "type declaration",
            ItemType::AssocTy => "associated type",
            ItemType::Interface => "[INTERFACE]",
            ItemType::Constant => "constant",
            ItemType::Unsupported(_) => "[OTHER]",
        }
    }
}

pub fn item_type(tcx: TyCtxt<'_>, def_id: DefId) -> ItemType {
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

pub fn inputs_and_output<'tcx>(
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

pub fn signature_of<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
) -> Signature {
    debug!("signature_of {def_id:?}");
    let (inputs, output) = inputs_and_output(ctx.tcx, def_id);

    let id = if !def_id.is_local() &&
        let Some(assoc) = ctx.opt_associated_item(def_id) &&
        let Some(id) = assoc.trait_item_def_id &&
        ctx.extern_spec(id).is_some() {
        id
    } else {
        def_id
    };

    let mut contract = names.with_public_clones(|names| {
        let pre_contract = crate::specification::contract_of(ctx, def_id);
        pre_contract.to_exp(ctx, names, id)
    });

    let subst = InternalSubsts::identity_for_item(ctx.tcx, def_id);

    if output.is_never() {
        contract.ensures.push(Exp::Const(Constant::const_false()));
    }

    if let TyKind::Closure(_, subst) = ctx.tcx.type_of(def_id).kind() {
        let post_subst = names.with_public_clones(|names| {
            closure_capture_subst(ctx.tcx, names, def_id, subst, subst.as_closure().kind(), false)
        });
        let pre_subst = names.with_public_clones(|names| {
            closure_capture_subst(ctx.tcx, names, def_id, subst, subst.as_closure().kind(), true)
        });
        contract.visit_mut(pre_subst, post_subst.clone(), post_subst);
    }

    let name = item_name(ctx.tcx, def_id, Namespace::ValueNS);

    let span = ctx.tcx.def_span(def_id);

    let mut args: Vec<Binder> = names.with_public_clones(|names| {
        inputs
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
        // TODO: Change arguments to be patterns not identifiers
        args.push(Binder::wild(Type::UNIT));
    };

    let mut attrs = why3_attrs(ctx.tcx, def_id);
    if matches!(item_type(ctx.tcx, def_id), ItemType::Program | ItemType::Closure) {
        attrs.push(declaration::Attribute::Attr("cfg:stackify".into()))
    };

    let retty = names.with_public_clones(|names| {
        translation::ty::translate_ty(ctx, names, span, EarlyBinder(output).subst(ctx.tcx, subst))
    });
    Signature { name, attrs, retty: Some(retty), args, contract }
}

use creusot_rustc::ast::{
    token::TokenKind::Literal,
    tokenstream::{TokenStream, TokenTree::*},
};

pub fn ts_to_symbol(ts: TokenStream) -> Option<Symbol> {
    assert_eq!(ts.len(), 1);

    if let Token(tok, _) = ts.trees().next().unwrap() {
        if let Literal(lit) = tok.kind {
            return Some(lit.symbol);
        }
    }
    None
}

pub fn get_attr<'a>(attrs: &'a [Attribute], path: &[&str]) -> Option<&'a AttrItem> {
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

pub fn get_attrs<'a>(attrs: &'a [Attribute], path: &[&str]) -> Vec<&'a Attribute> {
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

pub fn is_attr(attr: &Attribute, str: &str) -> bool {
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

#[derive(Clone)]
pub struct ClosureSubst(HashMap<Ident, (Exp, bool)>, ty::ClosureKind, bool);

impl<'a> ExpMutVisitor for ClosureSubst {
    fn visit_mut(&mut self, exp: &mut Exp) {
        match exp {
            Exp::Old(box Exp::Var(v, _)) => {
                if let Some((e, is_bor)) = self.0.get(v) {
                    let arg = if self.1 == ty::ClosureKind::FnMut {
                        Exp::Current(box Exp::pure_var(Ident::build("_1'")))
                    } else {
                        Exp::pure_var(Ident::build("_1'"))
                    };

                    let e = e.clone().app_to(arg);

                    if *is_bor {
                        *exp = Exp::Current(box e)
                    } else {
                        *exp = e
                    }
                }
            }
            Exp::Var(v, _) => {
                if let Some((e, is_bor)) = self.0.get(v) {
                    let arg = if self.1 == ty::ClosureKind::FnMut {
                        if self.2 {
                            Exp::Current(box Exp::pure_var(Ident::build("_1'")))
                        } else {
                            Exp::Final(box Exp::pure_var(Ident::build("_1'")))
                        }
                    } else {
                        Exp::pure_var(Ident::build("_1'"))
                    };

                    let e = e.clone().app_to(arg);

                    if *is_bor {
                        *exp = Exp::Current(box e)
                    } else {
                        *exp = e
                    }
                }
            }
            Exp::Abs(binders, body) => {
                let mut subst = self.0.clone();

                for binder in binders {
                    binder.fvs().into_iter().for_each(|id| {
                        subst.remove(&id);
                    });
                }

                std::mem::swap(&mut self.0, &mut subst);
                self.visit_mut(body);
                std::mem::swap(&mut self.0, &mut subst);
            }

            Exp::Let { pattern, arg, body } => {
                self.visit_mut(arg);
                let mut bound = pattern.binders();
                let mut subst = self.0.clone();
                bound.drain(..).for_each(|k| {
                    subst.remove(&k);
                });

                std::mem::swap(&mut self.0, &mut subst);
                self.visit_mut(body);
                std::mem::swap(&mut self.0, &mut subst);
            }
            Exp::Match(box scrut, brs) => {
                self.visit_mut(scrut);

                for (pat, br) in brs {
                    let mut s = self.0.clone();
                    pat.binders().drain(..).for_each(|b| {
                        s.remove(&b);
                    });

                    std::mem::swap(&mut self.0, &mut s);
                    self.visit_mut(br);
                    std::mem::swap(&mut self.0, &mut s);
                }
            }
            Exp::Forall(binders, exp) => {
                let mut subst = self.0.clone();
                binders.iter().for_each(|k| {
                    subst.remove(&k.0);
                });

                std::mem::swap(&mut self.0, &mut subst);
                self.visit_mut(exp);
                std::mem::swap(&mut self.0, &mut subst);
            }
            Exp::Exists(binders, exp) => {
                let mut subst = self.0.clone();
                binders.iter().for_each(|k| {
                    subst.remove(&k.0);
                });

                std::mem::swap(&mut self.0, &mut subst);
                self.visit_mut(exp);
                std::mem::swap(&mut self.0, &mut subst);
            }
            _ => super_visit_mut(self, exp),
        }
    }
}
pub fn closure_capture_subst<'tcx>(
    tcx: TyCtxt<'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
    cs: SubstsRef<'tcx>,
    // What kind of substitution we should generate. The same precondition can be used in several ways
    ck: ty::ClosureKind,
    precond: bool,
) -> ClosureSubst {
    let mut fun_def_id = def_id;
    while tcx.is_closure(fun_def_id) {
        fun_def_id = tcx.parent(fun_def_id);
    }

    let capture_names =
        tcx.symbols_for_closure_captures((fun_def_id.expect_local(), def_id.expect_local()));
    let captures = capture_names.iter().zip(cs.as_closure().upvar_tys());
    let subst = captures
        .into_iter()
        .enumerate()
        .map(|(ix, (nm, ty))| {
            // todo
            let acc_name = closure_accessor_name(tcx, def_id, ix);
            let acc = Exp::impure_qvar(names.insert(def_id, cs).qname_ident(acc_name));
            (nm.as_str().into(), (acc, ty.is_mutable_ptr()))
        })
        .collect();
    ClosureSubst(subst, ck, precond)
}
