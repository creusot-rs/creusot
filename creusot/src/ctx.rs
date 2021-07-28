use indexmap::IndexSet;
use std::collections::BTreeMap;

use why3::declaration::{CloneSubst, Decl, DeclClone, Predicate, TyDecl};
use why3::mlcfg::QName;

use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, subst::SubstsRef, TyCtxt};
use rustc_session::Session;
use rustc_span::Span;

use rustc_hir::definitions::DefPathData;
use rustc_resolve::Namespace;

use crate::modules::Modules;

use rustc_interface::interface::BoxedResolver;
use std::{cell::RefCell, rc::Rc};

pub struct NameMap<'tcx>(TyCtxt<'tcx>, BTreeMap<(DefId, SubstsRef<'tcx>), String>);

impl<'tcx> NameMap<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        NameMap(tcx, BTreeMap::new())
    }

    pub fn name_for(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> (bool, String) {
        if let Some(nm) = self.1.get(&(def_id, subst)) {
            (false, nm.clone())
        } else {
            let num_entries = self.1.len();
            let name_base = self.0.item_name(def_id).as_str().to_camel_case();
            self.1.insert((def_id, subst), format!("{}{}", name_base, num_entries));
            (true, self.1[&(def_id, subst)].clone())
        }
    }

    pub fn into_iter(self) -> impl Iterator<Item = ((DefId, SubstsRef<'tcx>), String)> {
        self.1.into_iter()
    }
}

pub struct TranslationCtx<'sess, 'tcx> {
    pub sess: &'sess Session,
    pub tcx: TyCtxt<'tcx>,
    pub used_tys: IndexSet<DefId>,
    pub used_traits: IndexSet<DefId>,
    pub translated_funcs: IndexSet<DefId>,
    pub modules: Modules,

    // Name resolution context for specs
    pub resolver: Rc<RefCell<BoxedResolver>>,
}

impl<'tcx, 'sess> TranslationCtx<'sess, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        sess: &'sess Session,
        resolver: Rc<RefCell<BoxedResolver>>,
    ) -> Self {
        Self {
            sess,
            tcx,
            used_tys: IndexSet::new(),
            used_traits: IndexSet::new(),
            translated_funcs: IndexSet::new(),
            resolver,
            modules: Modules::new(),
        }
    }

    pub fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub fn add_type(&mut self, ty_decl: TyDecl, drop_pred: Predicate) {
        self.modules.add_type(ty_decl, drop_pred);
    }
}

pub fn clone_item<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
    clone_name: String,
) -> why3::declaration::Decl {
    let clone_subst = type_param_subst(ctx, def_id, subst);

    Decl::Clone(DeclClone {
        name: cloneable_name(ctx.tcx, def_id),
        subst: clone_subst,
        as_nm: Some(clone_name),
    })
}

pub fn type_param_subst<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Vec<CloneSubst> {
    use heck::SnakeCase;
    use rustc_middle::ty::GenericParamDefKind;

    let trait_params = ctx.tcx.generics_of(def_id);
    let mut clone_subst = Vec::new();

    if subst.is_empty() {
        return Vec::new();
    }

    for ix in 0..trait_params.count() {
        let p = trait_params.param_at(ix, ctx.tcx);
        let ty = subst[ix];
        if let GenericParamDefKind::Type { .. } = p.kind {
            let ty = super::ty::translate_ty(ctx, rustc_span::DUMMY_SP, ty.expect_ty());
            clone_subst.push(CloneSubst::Type(p.name.to_string().to_snake_case().into(), ty));
        }
    }
    clone_subst
}

use heck::CamelCase;

pub fn translate_type_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, true)
}

pub fn translate_value_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, false)
}

pub fn cloneable_name(tcx: TyCtxt, def_id: DefId) -> QName {
    let qname = translate_value_id(tcx, def_id);
    use rustc_hir::def::DefKind::*;

    match tcx.def_kind(def_id) {
        Trait => qname,
        _ => qname.module_name(),
    }
}

fn translate_defid(tcx: TyCtxt, def_id: DefId, ty: bool) -> QName {
    let def_path = tcx.def_path(def_id);

    let mut segments = Vec::new();

    if def_path.krate.as_u32() != 0 {
        segments.push(tcx.crate_name(def_id.krate).to_string().to_camel_case())
    }

    for seg in def_path.data[..].iter() {
        match seg.data {
            // DefPathData::CrateRoot => segments.push(tcx.crate_name(def_id.krate).to_string()),
            // CORE ASSUMPTION: Once we stop seeing TypeNs we never see it again.
            DefPathData::Ctor => {}
            _ => segments.push(format!("{}", seg).to_camel_case()),
        }
    }

    let kind = tcx.def_kind(def_id);
    use rustc_hir::def::DefKind::*;

    let is_trait_assoc = if let Some(it) = tcx.opt_associated_item(def_id) {
        if let ty::TraitContainer(_) = it.container {
            true
        } else {
            false
        }
    } else {
        false
    };

    let name;
    match (kind, kind.ns()) {
        (_, _) if ty => {
            name = segments.into_iter().map(|seg| seg.to_lowercase()).collect();
            segments = vec!["Type".to_owned()];
        }
        (Ctor(_, _) | Variant | Struct, _) => {
            segments[0] = segments[0].to_camel_case();
            name = segments;
            segments = vec!["Type".to_owned()];
        }
        (Trait | Mod | Impl, _) => {
            name = segments;
            segments = Vec::new();
        }
        (_, Some(Namespace::ValueNS)) => {
            if is_trait_assoc {
                name = vec![segments.pop().unwrap().to_lowercase()];
            } else {
                name = vec!["impl".into()];
            }
        }
        (a, b) => unreachable!("{:?} {:?} {:?}", a, b, segments),
    }
    let module = if segments.is_empty() { Vec::new() } else { vec![segments.join("_")] };

    QName { module, name: name.join("_") }
}
