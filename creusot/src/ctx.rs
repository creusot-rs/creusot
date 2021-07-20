use indexmap::IndexSet;
use std::collections::BTreeMap;

use why3::declaration::{CloneSubst, Decl, DeclClone, Predicate, TyDecl};
use why3::mlcfg::QName;

use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::subst::SubstsRef;
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use rustc_span::Span;

use rustc_hir::definitions::DefPathData;
use rustc_resolve::Namespace;

use crate::modules::Modules;

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
}

impl<'tcx, 'sess> TranslationCtx<'sess, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'sess Session) -> Self {
        Self {
            sess,
            tcx,
            used_tys: IndexSet::new(),
            used_traits: IndexSet::new(),
            translated_funcs: IndexSet::new(),
            modules: Modules::new(),
        }
    }

    pub fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub fn add_type(&mut self, ty_decl: TyDecl, drop_pred: Predicate) {
        self.modules.add_type(ty_decl, drop_pred);
    }

    pub fn clone_item(
        &mut self,
        name_map: &mut NameMap<'tcx>,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
    ) -> why3::declaration::Decl {
        let clone_subst = self.type_param_subst(def_id, subst);
        let (_, clone_name) = name_map.name_for(def_id, subst);

        Decl::Clone(DeclClone {
            name: translate_value_id(self.tcx, def_id),
            subst: clone_subst,
            as_nm: Some(clone_name),
        })
    }

    pub fn type_param_subst(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> Vec<CloneSubst> {
        use heck::SnakeCase;
        use rustc_middle::ty::GenericParamDefKind;

        let trait_params = self.tcx.generics_of(def_id);
        let mut clone_subst = Vec::new();

        for ix in 0..trait_params.count() {
            let p = trait_params.param_at(ix, self.tcx);
            let ty = subst[ix];
            if let GenericParamDefKind::Type { .. } = p.kind {
                let ty = super::ty::translate_ty(self, rustc_span::DUMMY_SP, ty.expect_ty());
                clone_subst.push(CloneSubst::Type(p.name.to_string().to_snake_case().into(), ty));
            }
        }
        clone_subst
    }
}

use heck::CamelCase;

pub fn translate_type_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, true)
}

pub fn translate_value_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, false)
}

fn translate_defid(tcx: TyCtxt, def_id: DefId, ty: bool) -> QName {
    let def_path = tcx.def_path(def_id);

    let mut mod_segs = Vec::new();
    let mut name_segs = Vec::new();

    if def_path.krate.as_u32() != 0 {
        mod_segs.push(tcx.crate_name(def_id.krate).to_string().to_camel_case())
    }

    for seg in def_path.data[..].iter() {
        match seg.data {
            // DefPathData::CrateRoot => mod_segs.push(tcx.crate_name(def_id.krate).to_string()),
            DefPathData::TypeNs(_) => mod_segs.push(format!("{}", seg)[..].to_camel_case()),
            // CORE ASSUMPTION: Once we stop seeing TypeNs we never see it again.
            DefPathData::Ctor => {}
            _ => name_segs.push(format!("{}", seg)[..].to_camel_case()),
        }
    }

    let kind = tcx.def_kind(def_id);
    use rustc_hir::def::DefKind::*;

    match (kind, kind.ns()) {
        (_, _) if ty => {
            assert_eq!(name_segs.len(), 0);
            name_segs = mod_segs.into_iter().map(|seg| seg.to_lowercase()).collect();
            mod_segs = vec!["Type".to_owned()];
        }
        (Ctor(_, _) | Variant | Struct, _) => {
            mod_segs.append(&mut name_segs);
            mod_segs[0] = mod_segs[0].to_camel_case();
            name_segs = mod_segs;
            mod_segs = vec!["Type".to_owned()];
        }
        (Trait, _) => {
            assert_eq!(name_segs.len(), 0);
            name_segs = vec![mod_segs.pop().unwrap()];
        }
        (Mod | Impl, _) => {}
        (_, Some(Namespace::ValueNS)) => {
            mod_segs.extend(name_segs);
            name_segs = vec!["impl".into()];
        }
        (a, b) => unreachable!("{:?} {:?} {:?} {:?}", a, b, mod_segs, name_segs),
    }

    QName { module: mod_segs, name: name_segs.join("_") }
}
