use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{
        subst::SubstsRef, ProjectionTy, Ty, TyCtxt, TyKind, TypeSuperVisitable, TypeVisitor,
    },
    resolve::Namespace,
    span::Symbol,
};
use heck::ToUpperCamelCase;
use indexmap::IndexMap;
use why3::{declaration::CloneKind, Ident, QName};

use crate::{
    ctx::*,
    util::{self, item_name},
};

// Prelude modules
#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum PreludeModule {
    Float32,
    Float64,
    Int,
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    Isize,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    Usize,
    Char,
    Single,
    Double,
    Bool,
    Borrow,
    Slice,
    Opaque,
    Ref,
    Seq,
    Type,
}

impl PreludeModule {
    fn qname(&self) -> QName {
        match self {
            PreludeModule::Float32 => QName::from_string("ieee_float.Float32").unwrap(),
            PreludeModule::Float64 => QName::from_string("ieee_float.Float64").unwrap(),
            PreludeModule::Int => QName::from_string("mach.int.Int").unwrap(),
            PreludeModule::Int8 => QName::from_string("prelude.Int8").unwrap(),
            PreludeModule::Int16 => QName::from_string("prelude.Int16").unwrap(),
            PreludeModule::Int32 => QName::from_string("mach.int.Int32").unwrap(),
            PreludeModule::Int64 => QName::from_string("mach.int.Int64").unwrap(),
            PreludeModule::Int128 => QName::from_string("prelude.Int128").unwrap(),
            PreludeModule::UInt8 => QName::from_string("prelude.UInt8").unwrap(),
            PreludeModule::UInt16 => QName::from_string("prelude.UInt16").unwrap(),
            PreludeModule::UInt32 => QName::from_string("mach.int.UInt32").unwrap(),
            PreludeModule::UInt64 => QName::from_string("mach.int.UInt64").unwrap(),
            PreludeModule::UInt128 => QName::from_string("prelude.UInt128").unwrap(),
            PreludeModule::Char => QName::from_string("prelude.Char").unwrap(),
            PreludeModule::Single => QName::from_string("floating_point.Single").unwrap(),
            PreludeModule::Double => QName::from_string("floating_point.Double").unwrap(),
            PreludeModule::Opaque => QName::from_string("prelude.Opaque").unwrap(),
            PreludeModule::Ref => QName::from_string("Ref").unwrap(),
            PreludeModule::Seq => QName::from_string("seq.Seq").unwrap(),
            PreludeModule::Type => QName::from_string("Type").unwrap(),
            PreludeModule::Isize => QName::from_string("prelude.IntSize").unwrap(),
            PreludeModule::Usize => QName::from_string("prelude.UIntSize").unwrap(),
            PreludeModule::Bool => QName::from_string("prelude.Bool").unwrap(),
            PreludeModule::Borrow => QName::from_string("prelude.Borrow").unwrap(),
            PreludeModule::Slice => QName::from_string("prelude.Slice").unwrap(),
        }
    }
}

type CloneNode<'tcx> = (DefId, SubstsRef<'tcx>);
pub(crate) type CloneSummary<'tcx> = IndexMap<(DefId, SubstsRef<'tcx>), CloneInfo<'tcx>>;

#[derive(Clone)]
pub(crate) struct CloneMap<'tcx> {
    tcx: TyCtxt<'tcx>,
    prelude: IndexMap<QName, bool>,
    pub(crate) names: IndexMap<CloneNode<'tcx>, CloneInfo<'tcx>>,

    // Track how many instances of a name already exist
    name_counts: IndexMap<Symbol, usize>,

    // DefId of the item which is cloning. Used for trait resolution
    self_id: DefId,

    // Index of the last cloned entry
    last_cloned: usize,

    // Internal state to determine whether clones should be public or not
    public: bool,
}

impl<'tcx> Drop for CloneMap<'tcx> {
    fn drop(&mut self) {
        if self.last_cloned != self.names.len() {
            debug!(
                "Dropping clone map with un-emitted clones. {:?} clones emitted of {:?} total {:?}",
                self.last_cloned,
                self.names.len(),
                self.self_id,
            );
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable, Hash)]
enum Kind {
    Named(Symbol),
    Hidden,
    Export,
    // Use,
}

impl Kind {
    pub(crate) fn qname_ident(&self, method: Ident) -> QName {
        let module = match &self {
            Kind::Named(name) => vec![name.to_string().into()],
            _ => Vec::new(),
        };
        QName { module, name: method }
    }
}

use creusot_rustc::macros::{TyDecodable, TyEncodable};

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
enum CloneOpacity {
    Transparent,
    Opaque,
    Default,
}

#[derive(Clone, Debug, TyEncodable, TyDecodable)]
pub(crate) struct CloneInfo<'tcx> {
    kind: Kind,
    additional_deps: Vec<(Symbol, (DefId, SubstsRef<'tcx>))>,
    cloned: bool,
    public: bool,
    opaque: CloneOpacity,
}

impl Into<CloneKind> for Kind {
    fn into(self) -> CloneKind {
        match self {
            Kind::Named(i) => CloneKind::Named(i.to_string().into()),
            Kind::Hidden => CloneKind::Bare,
            Kind::Export => CloneKind::Export,
        }
    }
}

impl<'tcx> CloneInfo<'tcx> {
    fn from_name(name: Symbol, public: bool) -> Self {
        CloneInfo {
            kind: Kind::Named(name),
            additional_deps: Vec::new(),
            cloned: false,
            public,
            opaque: CloneOpacity::Default,
        }
    }

    // TODO: When traits stop holding all functions we can remove the last two arguments
    fn qname(&self, tcx: TyCtxt, def_id: DefId) -> QName {
        self.qname_ident(match tcx.def_kind(def_id) {
            // DefKind::Closure => Ident::build("closure"),
            _ => item_name(tcx, def_id, Namespace::ValueNS),
        })
    }

    fn qname_ident(&self, method: Ident) -> QName {
        self.kind.qname_ident(method)
    }
}

impl<'tcx> CloneMap<'tcx> {
    pub(crate) fn insert(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> &mut CloneInfo<'tcx> {
        let subst = self.tcx.erase_regions(subst);

        let (def_id, subst) = self.closure_hack(def_id, subst);

        self.names.entry((def_id, subst)).or_insert_with(|| {
            let base_sym = match util::item_type(self.tcx, def_id) {
                ItemType::Impl => self.tcx.item_name(self.tcx.trait_id_of_impl(def_id).unwrap()),
                ItemType::Closure => Symbol::intern(&format!(
                    "closure{}",
                    self.tcx.def_path(def_id).data.last().unwrap().disambiguator
                )),
                _ => self.tcx.item_name(def_id),
            };

            let base = Symbol::intern(&base_sym.as_str().to_upper_camel_case());
            let count: usize = *self.name_counts.entry(base).and_modify(|c| *c += 1).or_insert(0);
            trace!("inserting {:?} {:?} as {}{}", def_id, subst, base, count);

            // if base.as_str() == "IntoIter" && count == 1 && self.clone_level == CloneLevel::Interface {
            //     panic!();
            // }
            let info =
                CloneInfo::from_name(Symbol::intern(&format!("{}{}", base, count)), self.public);
            info
        })
    }

    pub(crate) fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let tcx = self.tcx;
        self.insert(def_id, subst).qname(tcx, def_id)
    }

    pub(crate) fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let name = item_name(self.tcx, def_id, Namespace::TypeNS).to_string().to_lowercase();
        self.insert(def_id, subst).qname_ident(name.into())
    }

    pub(crate) fn import_prelude_module(&mut self, module: PreludeModule) {
        self.prelude.entry(module.qname()).or_insert(false);
    }

    pub(crate) fn import_builtin_module(&mut self, module: QName) {
        self.prelude.entry(module).or_insert(false);
    }

    fn closure_hack(&self, def_id: DefId, subst: SubstsRef<'tcx>) -> (DefId, SubstsRef<'tcx>) {
        if self.tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_unnest"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id)
        {
            trace!("closure_hack: {:?} {:?}", self.self_id, def_id);
            let self_ty = subst.types().nth(1).unwrap();
            if let TyKind::Closure(id, csubst) = self_ty.kind() {
                return (*id, csubst);
            }
        };

        if self.tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id)
            || self.tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
        {
            let self_ty = subst.types().nth(0).unwrap();
            if let TyKind::Closure(id, csubst) = self_ty.kind() {
                return (*id, csubst);
            }
        }

        (def_id, subst)
    }
}

struct ProjectionTyVisitor<'tcx, F: FnMut(&ProjectionTy<'tcx>)> {
    f: F,
    p: std::marker::PhantomData<&'tcx ()>,
}

impl<'tcx, F: FnMut(&ProjectionTy<'tcx>)> TypeVisitor<'tcx> for ProjectionTyVisitor<'tcx, F> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        match t.kind() {
            TyKind::Projection(pty) => {
                (self.f)(pty);
                t.super_visit_with(self)
            }
            _ => t.super_visit_with(self),
        }
    }
}
