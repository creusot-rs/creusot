use rustc_ast_ir::visit::VisitorResult;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_type_ir::{fold::TypeFoldable, visit::TypeVisitable, AliasTyKind, Interner};

use crate::{
    naming::{item_symb, translate_accessor_name, type_name, value_name},
    translation::traits,
    util::erased_identity_for_item,
};

use super::{structural_resolve, ty_inv::tyinv_head_and_subst, PreludeModule, TransId};

/// Dependencies between items and the resolution logic to find the 'monomorphic' forms accounting
/// for various Creusot hacks like the handling of closures.
///
/// These should be used both to power the cloning system and to order the overall translation of items in Creusot.
///

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, TypeVisitable, TypeFoldable)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item(DefId, GenericArgsRef<'tcx>),
    // Type invariants and structual resolution expressions
    // are identified by a substituted type, each of these entries is associated with a `TransId` containing a
    // 'skeleton type' (aka type with identity substs).
    TyInvAxiom(Ty<'tcx>),
    StructuralResolve(Ty<'tcx>),
    ClosureSpec(ClosureSpecKind, DefId, GenericArgsRef<'tcx>),
    Builtin(PreludeModule),
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
    Accessor(u8),
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
    pub(crate) fn new(tcx: TyCtxt<'tcx>, (did, subst): (DefId, GenericArgsRef<'tcx>)) -> Self {
        match tcx.def_kind(did) {
            DefKind::Enum | DefKind::Struct | DefKind::Union => {
                Dependency::Type(Ty::new_adt(tcx, tcx.adt_def(did), subst))
            }
            DefKind::AssocTy => Dependency::Type(Ty::new_projection(tcx, did, subst)),
            _ => {
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
                    if let TyKind::Closure(id, csubst) = self_ty.kind() {
                        return Dependency::ClosureSpec(closure_spec, *id, csubst);
                    }
                }

                if let Some(ty) = is_structural_resolve(tcx, (did, subst)) {
                    Dependency::StructuralResolve(ty)
                } else {
                    Dependency::Item(did, subst)
                }
            }
        }
    }

    pub(crate) fn from_trans_id(tcx: TyCtxt<'tcx>, trans_id: TransId<'tcx>) -> Self {
        match trans_id {
            TransId::Item(self_id) => {
                let subst = match tcx.def_kind(self_id) {
                    DefKind::Closure => match tcx.type_of(self_id).instantiate_identity().kind() {
                        TyKind::Closure(_, subst) => subst,
                        _ => unreachable!(),
                    },
                    _ => erased_identity_for_item(tcx, self_id),
                };

                Dependency::new(tcx, (self_id, subst)).erase_regions(tcx)
            }
            TransId::TyInvAxiom(ty) => Dependency::TyInvAxiom(ty),
            TransId::Hacked(h, self_id) => {
                let subst = match tcx.def_kind(self_id) {
                    DefKind::Closure => match tcx.type_of(self_id).instantiate_identity().kind() {
                        TyKind::Closure(_, subst) => subst,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };
                Dependency::ClosureSpec(h, self_id, subst).erase_regions(tcx)
            }
            TransId::StructuralResolve(ty) => Dependency::StructuralResolve(ty),
        }
    }

    pub(crate) fn to_trans_id(
        self,
        tcx: TyCtxt<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Option<TransId<'tcx>> {
        match self {
            Dependency::Type(_) => None,
            Dependency::Item(id, _) => Some(TransId::Item(id)),
            Dependency::TyInvAxiom(ty) => {
                let ty = tyinv_head_and_subst(tcx, ty, param_env).0;
                Some(TransId::TyInvAxiom(ty))
            }
            Dependency::ClosureSpec(h, id, _) => Some(TransId::Hacked(h, id)),
            Dependency::Builtin(_) => None,
            Dependency::StructuralResolve(ty) => {
                let ty = structural_resolve::head_and_subst(tcx, ty).0;
                Some(TransId::StructuralResolve(ty))
            }
        }
    }

    pub(crate) fn resolve(mut self, tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>) -> Self {
        if let Dependency::Item(item, substs) = self {
            self = resolve_item(item, substs, tcx, param_env);
        }
        tcx.normalize_erasing_regions(param_env, self)
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
            Dependency::TyInvAxiom(_) | Dependency::Builtin(_) => None,
            Dependency::StructuralResolve(_) => None,
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
                TyKind::Closure(def_id, _) => {
                    Some(item_symb(tcx, *def_id, rustc_hir::def::Namespace::TypeNS))
                }
                TyKind::Param(p) => Some(Symbol::intern(&type_name(p.name.as_str()))),
                _ => None,
            },
            Dependency::Item(_, _) => {
                let did = self.did().unwrap().0;
                match tcx.def_kind(did) {
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
                    _ => Some(Symbol::intern(&value_name(tcx.item_name(did).as_str()))),
                }
            }
            Dependency::ClosureSpec(hacked_id, _, _) => match hacked_id {
                ClosureSpecKind::PostconditionOnce => Some(Symbol::intern("postcondition_once")),
                ClosureSpecKind::PostconditionMut => Some(Symbol::intern("postcondition_mut")),
                ClosureSpecKind::Postcondition => Some(Symbol::intern("postcondition")),
                ClosureSpecKind::Precondition => Some(Symbol::intern("precondition")),
                ClosureSpecKind::Unnest => Some(Symbol::intern("unnest")),
                ClosureSpecKind::Resolve => Some(Symbol::intern("resolve")),
                ClosureSpecKind::Accessor(ix) => Some(Symbol::intern(&format!("field_{ix}"))),
            },
            Dependency::TyInvAxiom(..) => Some(Symbol::intern(&format!("inv_axiom"))),
            Dependency::StructuralResolve(_) => Some(Symbol::intern("structural_resolve")),
            Dependency::Builtin(_) => None,
        }
    }

    pub fn is_type(self) -> bool {
        matches!(self, Dependency::Type(_))
    }

    pub fn is_invariant(self) -> bool {
        matches!(self, Dependency::TyInvAxiom(_))
    }
}

fn resolve_item<'tcx>(
    item: DefId,
    substs: GenericArgsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Dependency<'tcx> {
    if tcx.trait_of_item(item).is_some()
        && let traits::TraitResol::Instance(did, subst) =
            traits::resolve_assoc_item_opt(tcx, param_env, item, substs)
    {
        Dependency::new(tcx, (did, subst))
    } else {
        // May happen:
        //    - if this is not a trait method, or
        //    - if don't know the instance
        Dependency::new(tcx, (item, substs))
    }
}

fn is_structural_resolve<'tcx>(
    tcx: TyCtxt<'tcx>,
    dep: (DefId, GenericArgsRef<'tcx>),
) -> Option<Ty<'tcx>> {
    if tcx.is_diagnostic_item(Symbol::intern("creusot_structural_resolve"), dep.0) {
        Some(dep.1.type_at(0))
    } else {
        None
    }
}
