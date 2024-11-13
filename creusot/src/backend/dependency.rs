use rustc_ast_ir::visit::VisitorResult;
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
use rustc_type_ir::{fold::TypeFoldable, visit::TypeVisitable, AliasTyKind, Interner};

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
    AllTyInvAxioms,
    ClosureSpec(ClosureSpecKind, DefId, GenericArgsRef<'tcx>),
    Builtin(PreludeModule),
    Eliminator(DefId, GenericArgsRef<'tcx>),
    Promoted(LocalDefId, Promoted),
}

/// Due to how rustc keeps closures hidden from us, some key symbols of creusot don't get their own def ids.
/// Instead, we use this enumerator combined with the closure's defid to distinguish these symbols.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub(crate) enum ClosureSpecKind {
    PostconditionOnce,
    PostconditionMut,
    Postcondition,
    Precondition,
    Unnest,
    Resolve,
    Accessor(u32),
}

impl<'tcx, I: Interner> TypeVisitable<I> for ClosureSpecKind {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<I>>(&self, _: &mut V) -> V::Result {
        V::Result::output()
    }
}

impl<'tcx, I: Interner> TypeFoldable<I> for ClosureSpecKind {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<I>>(
        self,
        _: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(self)
    }
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn item(tcx: TyCtxt<'tcx>, (did, subst): (DefId, GenericArgsRef<'tcx>)) -> Self {
        // We need to "overload" certain identifiers in rustc so that we can distinguish them while
        // rustc doesn't. In particular, closures act as both a type and a function and are missing many
        // identifiers for things like accessors.
        //
        // We also use this to overload "structural resolution" for types

        let closure_spec = tcx.get_diagnostic_name(did).and_then(|s| match s.as_str() {
            "fn_once_impl_precond" => Some((ClosureSpecKind::Precondition, 1)),
            "fn_once_impl_postcond" => Some((ClosureSpecKind::PostconditionOnce, 1)),
            "fn_mut_impl_postcond" => Some((ClosureSpecKind::PostconditionMut, 1)),
            "fn_impl_postcond" => Some((ClosureSpecKind::Postcondition, 1)),
            "fn_mut_impl_unnest" => Some((ClosureSpecKind::Unnest, 1)),
            "creusot_resolve_method" => Some((ClosureSpecKind::Resolve, 0)),
            _ => None,
        });

        if let Some((closure_spec, param_id)) = closure_spec {
            let self_ty = subst.types().nth(param_id).unwrap();
            if let TyKind::Closure(id, subst) = self_ty.kind() {
                return Dependency::ClosureSpec(closure_spec, *id, subst);
            }
        }

        Dependency::Item(did, subst)
    }

    pub(crate) fn did(self) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        match self {
            Dependency::Item(def_id, subst) => Some((def_id, subst)),
            Dependency::Type(t) => match t.kind() {
                TyKind::Adt(def, substs) => Some((def.did(), substs)),
                TyKind::Closure(id, substs) => Some((*id, substs)),
                TyKind::Alias(AliasTyKind::Projection, aty) => Some((aty.def_id, aty.args)),
                _ => None,
            },
            Dependency::ClosureSpec(_, id, substs) => Some((id, substs)),
            _ => None,
        }
    }

    pub(crate) fn is_closure_spec(&self) -> bool {
        matches!(self, Dependency::ClosureSpec(_, _, _))
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
            Dependency::ClosureSpec(spec_kind, _, _) => match spec_kind {
                ClosureSpecKind::PostconditionOnce => Some(Symbol::intern("postcondition_once")),
                ClosureSpecKind::PostconditionMut => Some(Symbol::intern("postcondition_mut")),
                ClosureSpecKind::Postcondition => Some(Symbol::intern("postcondition")),
                ClosureSpecKind::Precondition => Some(Symbol::intern("precondition")),
                ClosureSpecKind::Unnest => Some(Symbol::intern("unnest")),
                ClosureSpecKind::Resolve => Some(Symbol::intern("resolve")),
                ClosureSpecKind::Accessor(ix) => Some(Symbol::intern(&format!("field_{ix}"))),
            },
            Dependency::TyInvAxiom(..) => Some(Symbol::intern(&format!("inv_axiom"))),
            Dependency::Eliminator(did, _) => {
                Some(Symbol::intern(&value_name(&translate_name(tcx.item_name(did).as_str()))))
            }
            Dependency::Promoted(did, prom) => Some(Symbol::intern(&format!(
                "promoted{}__{}",
                prom.as_usize(),
                value_name(&translate_name(tcx.item_name(did.to_def_id()).as_str()))
            ))),
            Dependency::Builtin(_) | Dependency::AllTyInvAxioms => None,
        }
    }
}
