use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Promoted,
    ty::{GenericArgsRef, Ty, TyCtxt, TyKind},
};
use rustc_span::Symbol;
use rustc_type_ir::AliasTyKind;

use crate::{
    backend::PreludeModule,
    naming::{item_symb, translate_accessor_name, translate_name, type_name, value_name},
};

/// Dependencies between items and the resolution logic to find the 'monomorphic' forms accounting
/// for various Creusot hacks like the handling of closures.
///
/// These should be used both to power the cloning system and to order the overall translation of items in Creusot.
///

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, TypeVisitable, TypeFoldable)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item(DefId, GenericArgsRef<'tcx>),
    TyInvAxiom(Ty<'tcx>),
    ClosureAccessor(DefId, GenericArgsRef<'tcx>, u32),
    Builtin(PreludeModule),
    Eliminator(DefId, GenericArgsRef<'tcx>),
    Promoted(LocalDefId, Promoted),
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn did(self) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        match self {
            Dependency::Item(def_id, subst) => Some((def_id, subst)),
            Dependency::Type(t) => match t.kind() {
                TyKind::Adt(def, substs) => Some((def.did(), substs)),
                TyKind::Closure(id, substs) => Some((*id, substs)),
                TyKind::Alias(AliasTyKind::Projection, aty) => Some((aty.def_id, aty.args)),
                _ => None,
            },
            _ => None,
        }
    }

    // FIXME: this function should not be necessary, dependencies should not be created non-normalized
    pub(crate) fn erase_regions(self, tcx: TyCtxt<'tcx>) -> Self {
        tcx.erase_regions(self)
    }

    pub(crate) fn base_ident(self, tcx: TyCtxt<'tcx>) -> Option<Symbol> {
        match self {
            Dependency::Type(ty) => match ty.kind() {
                TyKind::Adt(def, _) if !def.is_box() => {
                    Some(item_symb(tcx, def.did(), rustc_hir::def::Namespace::TypeNS))
                }
                TyKind::Alias(_, aty) => {
                    Some(Symbol::intern(&type_name(tcx.item_name(aty.def_id).as_str())))
                }
                TyKind::Closure(def_id, _) => Some(Symbol::intern(&format!(
                    "closure{}",
                    tcx.def_path(*def_id).data.last().unwrap().disambiguator
                ))),
                TyKind::Param(p) => Some(Symbol::intern(&type_name(p.name.as_str()))),
                _ => None,
            },
            Dependency::Item(did, _) => match tcx.def_kind(did) {
                DefKind::Impl { .. } => Some(tcx.item_name(tcx.trait_id_of_impl(did).unwrap())),
                DefKind::Closure => Some(Symbol::intern(&format!(
                    "closure{}",
                    tcx.def_path(did).data.last().unwrap().disambiguator
                ))),
                DefKind::Field => {
                    let variant = tcx.parent(did);
                    let name = translate_accessor_name(
                        &tcx.item_name(variant).as_str(),
                        &tcx.item_name(did).as_str(),
                    );
                    Some(Symbol::intern(&name))
                }
                DefKind::Variant => Some(item_symb(tcx, did, rustc_hir::def::Namespace::ValueNS)),
                _ => {
                    Some(Symbol::intern(&value_name(&translate_name(tcx.item_name(did).as_str()))))
                }
            },
            Dependency::ClosureAccessor(_, _, ix) => Some(Symbol::intern(&format!("field_{ix}"))),
            Dependency::TyInvAxiom(..) => Some(Symbol::intern(&format!("inv_axiom"))),
            Dependency::Eliminator(did, _) => {
                Some(Symbol::intern(&value_name(&translate_name(tcx.item_name(did).as_str()))))
            }
            Dependency::Promoted(did, prom) => Some(Symbol::intern(&format!(
                "promoted{}__{}",
                prom.as_usize(),
                value_name(&translate_name(tcx.item_name(did.to_def_id()).as_str()))
            ))),
            Dependency::Builtin(_) => None,
        }
    }
}
