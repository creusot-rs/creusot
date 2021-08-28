use indexmap::{IndexSet, IndexMap};
use std::collections::BTreeMap;

use why3::declaration::{CloneSubst, Decl, DeclClone, Module, TyDecl};
use why3::mlcfg::QName;

use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, subst::SubstsRef, TyCtxt};
use rustc_session::Session;
use rustc_span::Span;

use rustc_hir::def::DefKind;
use rustc_hir::definitions::DefPathData;
use rustc_resolve::Namespace;

use crate::{util, options::Options};

pub struct NameMap<'tcx>(TyCtxt<'tcx>, BTreeMap<(DefId, SubstsRef<'tcx>), String>);

impl<'tcx> NameMap<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        NameMap(tcx, BTreeMap::new())
    }

    pub fn name_for(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> String {
        if let Some(nm) = self.1.get(&(def_id, subst)) {
            nm.clone()
        } else {
            let num_entries = self.1.len();
            let name_base = self.0.item_name(def_id).as_str().to_camel_case();
            self.1.insert((def_id, subst), format!("{}{}", name_base, num_entries));
            self.1[&(def_id, subst)].clone()
        }
    }

    pub fn qname_for(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let module = self.name_for(def_id, subst);

        QName { module: vec![module], name: method_name(self.0, def_id) }
    }

    pub fn into_iter(self) -> impl Iterator<Item = ((DefId, SubstsRef<'tcx>), String)> {
        self.1.into_iter()
    }
}

pub struct TranslationCtx<'sess, 'tcx> {
    pub sess: &'sess Session,
    pub tcx: TyCtxt<'tcx>,
    pub translated_items: IndexSet<DefId>,
    pub types: Vec<TyDecl>,
    pub functions: IndexMap<DefId, Module>,
    pub externs: IndexMap<DefId, Module>, 
    pub opts: &'sess Options,
}

impl<'tcx, 'sess> TranslationCtx<'sess, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        sess: &'sess Session,
        opts: &'sess Options,
    ) -> Self {
        Self {
            sess,
            tcx,
            translated_items: IndexSet::new(),
            types: Vec::new(),
            functions: IndexMap::new(),
            externs: IndexMap::new(),
            opts,
        }
    }

    // Generic entry point for function translation
    pub fn translate_function(&mut self, def_id: DefId) {
        if !self.translated_items.insert(def_id) {
            return;
        }

        if !crate::util::should_translate(self.tcx, def_id) {
            info!("Skipping {:?}", def_id);
            return;
        }

        let span = self.tcx.hir().span_if_local(def_id).unwrap_or(rustc_span::DUMMY_SP);
        let module = if !def_id.is_local() {
            debug!("translating {:?} as extern", def_id);
            crate::translation::translate_extern(self, def_id, span)
        } else if crate::translation::is_logic(self.tcx, def_id) {
            debug!("translating {:?} as logic", def_id);
            crate::translation::translate_logic(self, def_id, span)
        } else if crate::translation::is_predicate(self.tcx, def_id) {
            debug!("translating {:?} as predicate", def_id);
            crate::translation::translate_predicate(self, def_id, span)
        } else {
            let kind = self.tcx.def_kind(def_id);
            if kind == DefKind::Fn || kind == DefKind::Closure || kind == DefKind::AssocFn {
                let is_spec = util::is_invariant(self.tcx, def_id);
                if is_spec {
                    return;
                }

                crate::translation::translate_function(self.tcx, self, def_id)
            } else {
                unimplemented!("{:?} {:?}", def_id, self.tcx.def_kind(def_id))
            }
        };

        self.functions.insert(def_id, module);
    }

    pub fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub fn warn(&self, span: Span, msg: &str) {
        self.sess.span_warn_with_code(
            span,
            msg,
            DiagnosticId::Lint {
                name: String::from("creusot"),
                has_future_breakage: false,
                is_force_warn: true,
            },
        )
    }

    pub fn add_type(&mut self, decl: TyDecl) {
        let mut dependencies = decl.used_types();
        let mut pos = 0;
        while !dependencies.is_empty() && pos < self.types.len() {
            dependencies.remove(&self.types[pos].ty_name);
            pos += 1;
        }

        self.types.insert(pos, decl);
    }

    pub fn should_export(&self) -> bool {
        self.opts.export_metadata
    }

    pub fn should_compile(&self) -> bool {
        ! self.opts.dependency
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

fn method_name(tcx: TyCtxt, def_id: DefId) -> String {
    if let Some(it) = tcx.opt_associated_item(def_id) {
        if let ty::TraitContainer(_) = it.container {
            tcx.item_name(def_id).to_string().to_lowercase()
        } else {
            "impl".into()
        }
    } else {
        "impl".into()
    }
}

fn translate_defid(tcx: TyCtxt, def_id: DefId, ty: bool) -> QName {
    let def_path = tcx.def_path(def_id);

    let mut segments = Vec::new();

    segments.push(tcx.crate_name(def_id.krate).to_string().to_camel_case());

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
        (_, Some(Namespace::ValueNS)) | (Closure, _) => {
            // temporary hack, if the method belongs to a trait declaration pop off last segment
            let is_trait_assoc = method_name(tcx, def_id) != "impl";

            if is_trait_assoc {
                segments.pop().unwrap();
            }

            name = vec![method_name(tcx, def_id)];
        }
        (a, b) => unreachable!("{:?} {:?} {:?}", a, b, segments),
    }
    let module = if segments.is_empty() { Vec::new() } else { vec![segments.join("_")] };

    QName { module, name: name.join("_") }
}
