use indexmap::{IndexMap, IndexSet};

use why3::declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use};
use why3::QName;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    self,
    subst::{InternalSubsts, SubstsRef},
    TyCtxt,
};

use heck::CamelCase;

use crate::ctx::{self, *};

// Prelude modules
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PreludeModule {
    Int,
    Int32,
    Int64,
    UInt32,
    UInt64,
    Char,
    Single,
    Double,
    Prelude,
    Ref,
    Type,
}

impl PreludeModule {
    fn qname(&self) -> QName {
        match self {
            PreludeModule::Int => QName::from_string("mach.int.Int").unwrap(),
            PreludeModule::Int32 => QName::from_string("mach.int.Int32").unwrap(),
            PreludeModule::Int64 => QName::from_string("mach.int.Int64").unwrap(),
            PreludeModule::UInt32 => QName::from_string("mach.int.UInt32").unwrap(),
            PreludeModule::UInt64 => QName::from_string("mach.int.UInt64").unwrap(),
            PreludeModule::Char => QName::from_string("string.Char").unwrap(),
            PreludeModule::Single => QName::from_string("floating_point.Single").unwrap(),
            PreludeModule::Double => QName::from_string("floating_point.Double").unwrap(),
            PreludeModule::Prelude => QName::from_string("prelude.Prelude").unwrap(),
            PreludeModule::Ref => QName::from_string("Ref").unwrap(),
            PreludeModule::Type => QName::from_string("Type").unwrap(),
        }
    }
}

pub struct CloneMap<'tcx> {
    tcx: TyCtxt<'tcx>,
    prelude: IndexSet<PreludeModule>,
    names: IndexMap<(DefId, SubstsRef<'tcx>), CloneInfo>,
    count: usize,
}

#[derive(Clone)]
pub struct CloneInfo {
    name: String,
    projs: Vec<CloneSubst>,
    hidden: bool,
}

impl CloneInfo {
    fn from_name(name: String) -> Self {
        CloneInfo { name, projs: Vec::new(), hidden: false }
    }

    fn hidden(name: String) -> Self {
        CloneInfo { name, projs: Vec::new(), hidden: true }
    }

    // TODO: When traits stop holding all functions we can remove the last two arguments
    pub fn qname(&self, tcx: TyCtxt, def_id: DefId) -> QName {
        QName { module: vec![self.name.clone()], name: ctx::method_name(tcx, def_id) }
    }
}

impl<'tcx> CloneMap<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let names = IndexMap::new();
        CloneMap { tcx, names, count: 0, prelude: IndexSet::new() }
    }

    pub fn insert(&mut self, mut def_id: DefId, subst: SubstsRef<'tcx>) -> &CloneInfo {
        if let Some(it) = self.tcx.opt_associated_item(def_id) {
            if let ty::TraitContainer(_) = it.container {
                def_id = it.container.id()
            }
        };

        let tcx = self.tcx;
        let count = &mut self.count;
        self.names.entry((def_id, subst)).or_insert_with(|| {
            let name_base = tcx.item_name(def_id).as_str().to_camel_case();
            let info = CloneInfo::from_name(format!("{}{}", name_base, count));
            *count += 1;
            info
        })
    }

    pub fn qname_for_mut(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let tcx = self.tcx;
        let module = self.insert(def_id, subst);
        module.qname(tcx, def_id)
    }

    pub fn clone_self(&mut self, self_id: DefId) {
        let mut modl = ctx::translate_value_id(self.tcx, self_id);
        let clone_name = if modl.module.is_empty() { modl.name } else { modl.module.remove(0) };
        let subst = InternalSubsts::identity_for_item(self.tcx, self_id);
        self.names.insert((self_id, subst), CloneInfo::hidden(clone_name));
    }

    pub fn clone_with_extra_substs(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
        extra: Vec<CloneSubst>,
    ) {
        let _ = self.qname_for_mut(def_id, subst);

        if let Some(info) = self.names.get_mut(&(def_id, subst)) {
            info.projs.extend(extra);
        } else {
            unreachable!("clone_with_projs: no clone for def_id={:?}, subst={:?}", def_id, subst);
        }
    }

    pub fn import_prelude_module(&mut self, module: PreludeModule) {
        self.prelude.insert(module);
    }

    pub fn is_empty(&self) -> bool {
        self.names.len() <= 1
    }

    pub fn into_iter(self) -> impl Iterator<Item = ((DefId, SubstsRef<'tcx>), String)> {
        self.names.into_iter().skip(1).map(|(k, i)| (k, i.name))
    }

    pub fn to_clones(mut self, ctx: &mut ctx::TranslationCtx<'_, 'tcx>) -> Vec<Decl> {
        let mut i = 0;
        let mut decls = Vec::new();

        while i < self.names.len() {
            let ((def_id, subst), clone_info) = self.names.get_index(i).unwrap();
            i += 1;

            if clone_info.hidden {
                continue;
            }

            // hack to force borrow to end now.
            let clone_info = clone_info.clone();
            let def_id = *def_id;
            let subst = *subst;

            decls.push(clone_item(ctx, &mut self, def_id, subst, clone_info));
        }

        self.prelude
            .into_iter()
            .map(|q| Decl::UseDecl(Use { name: q.qname() }))
            .chain(decls.into_iter())
            .collect()
    }
}

fn clone_item<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
    info: CloneInfo,
) -> why3::declaration::Decl {
    let mut clone_subst = type_param_subst(ctx, names, def_id, subst);

    clone_subst.extend(info.projs);

    // Append each projection to this.

    Decl::Clone(DeclClone {
        name: cloneable_name(ctx.tcx, def_id),
        subst: clone_subst,
        kind: CloneKind::Named(info.name),
    })
}

// Create the substitution used to clone `def_id` with the rustc substitution `subst`.
pub fn type_param_subst<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
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
            let ty = super::ty::translate_ty(ctx, names, rustc_span::DUMMY_SP, ty.expect_ty());
            clone_subst.push(CloneSubst::Type(p.name.to_string().to_snake_case().into(), ty));
        }
    }

    clone_subst
}
