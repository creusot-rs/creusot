use rustc_ast_ir::visit::VisitorResult;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{EarlyBinder, GenericArgs, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_type_ir::{fold::TypeFoldable, visit::TypeVisitable, AliasTyKind, Interner};

use crate::{
    ctx::TranslationCtx,
    translation::traits,
    util::{self, item_symb, translate_accessor_name, type_name, value_name, ItemType},
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
    TyInv(Ty<'tcx>),
    StructuralResolve(Ty<'tcx>),
    Hacked(ExtendedId, DefId, GenericArgsRef<'tcx>),
    Builtin(PreludeModule),
}

/// Due to how rustc keeps closures hidden from us, some key symbols of creusot don't get their own def ids.
/// Instead, we use this enumerator combined with the closure's defid to distinguish these symbols.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub(crate) enum ExtendedId {
    PostconditionOnce,
    PostconditionMut,
    Postcondition,
    Precondition,
    Unnest,
    Resolve,
    Accessor(u8),
}

impl<'tcx, I: Interner> TypeVisitable<I> for ExtendedId {
    fn visit_with<V: rustc_type_ir::visit::TypeVisitor<I>>(&self, _: &mut V) -> V::Result {
        V::Result::output()
    }
}

impl<'tcx, I: Interner> TypeFoldable<I> for ExtendedId {
    fn try_fold_with<F: rustc_type_ir::fold::FallibleTypeFolder<I>>(
        self,
        _: &mut F,
    ) -> Result<Self, F::Error> {
        Ok(self)
    }
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, (did, subst): (DefId, GenericArgsRef<'tcx>)) -> Self {
        match util::item_type(tcx, did) {
            ItemType::Type => Dependency::Type(Ty::new_adt(tcx, tcx.adt_def(did), subst)),
            ItemType::AssocTy => Dependency::Type(Ty::new_projection(tcx, did, subst)),
            _ => Dependency::Item(did, subst),
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
                    _ => GenericArgs::identity_for_item(tcx, self_id),
                };

                Dependency::new(tcx, (self_id, subst)).erase_regions(tcx)
            }
            TransId::TyInv(ty) => Dependency::TyInv(ty),
            TransId::Hacked(h, self_id) => {
                let subst = match tcx.def_kind(self_id) {
                    DefKind::Closure => match tcx.type_of(self_id).instantiate_identity().kind() {
                        TyKind::Closure(_, subst) => subst,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };
                Dependency::Hacked(h, self_id, subst).erase_regions(tcx)
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
            Dependency::TyInv(ty) => {
                let ty = tyinv_head_and_subst(tcx, ty, param_env).0;
                Some(TransId::TyInv(ty))
            }
            Dependency::Hacked(h, id, _) => Some(TransId::Hacked(h, id)),
            Dependency::Builtin(_) => None,
            Dependency::StructuralResolve(ty) => {
                let ty = structural_resolve::head_and_subst(tcx, ty).0;
                Some(TransId::StructuralResolve(ty))
            }
        }
    }

    pub(crate) fn resolve(
        mut self,
        ctx: &TranslationCtx<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Option<Self> {
        if let Dependency::Item(item, substs) = self {
            self = resolve_item(item, substs, ctx.tcx, param_env);
        }

        ctx.try_normalize_erasing_regions(param_env, self).ok()
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
            Dependency::Hacked(_, id, substs) => Some((id, substs)),
            Dependency::TyInv(_) | Dependency::Builtin(_) => None,
            Dependency::StructuralResolve(_) => None,
        }
    }

    pub(crate) fn is_hacked(&self) -> bool {
        matches!(self, Dependency::Hacked(_, _, _))
    }

    #[inline]
    pub(crate) fn erase_regions(self, tcx: TyCtxt<'tcx>) -> Self {
        tcx.erase_regions(self)
    }

    #[inline]
    pub(crate) fn subst(
        self,
        tcx: TyCtxt<'tcx>,
        other: Dependency<'tcx>,
        param_env: ParamEnv<'tcx>,
    ) -> Self {
        let substs = if let Dependency::TyInv(ty) = other {
            tyinv_head_and_subst(tcx, ty, param_env).1
        } else if let Dependency::StructuralResolve(ty) = other {
            structural_resolve::head_and_subst(tcx, ty).1
        } else if let Some((_, substs)) = other.did() {
            substs
        } else {
            return self;
        };

        EarlyBinder::bind(self).instantiate(tcx, substs)
    }

    /// We need to "overload" certain identifiers in rustc so that we can distinguish them while
    /// rustc doesn't. In particular, closures act as both a type and a function and are missing many
    /// identifiers for things like accessors.
    ///
    /// We also use this to overload "structural resolution" for types
    #[inline]
    pub(crate) fn identify_overloads(self, tcx: TyCtxt<'tcx>) -> Self {
        match self {
            Dependency::Item(did, subst) => {
                let (hacked_id, id, subst) = closure_hack(tcx, did, subst);
                if let Some(hacked_id) = hacked_id {
                    Dependency::Hacked(hacked_id, id, subst)
                } else if let Some(ty) = structural_resolve(tcx, (id, subst)) {
                    Dependency::StructuralResolve(ty)
                } else {
                    Dependency::new(tcx, (id, subst))
                }
            }

            _ => self,
        }
    }

    pub(crate) fn base_ident(self, tcx: TyCtxt<'tcx>) -> Symbol {
        match self {
            Dependency::Type(ty) => match ty.kind() {
                TyKind::Adt(def, _) => item_symb(tcx, def.did(), rustc_hir::def::Namespace::TypeNS),
                TyKind::Alias(_, aty) => {
                    Symbol::intern(&type_name(tcx.item_name(aty.def_id).as_str()))
                }
                TyKind::Closure(def_id, _) => {
                    item_symb(tcx, *def_id, rustc_hir::def::Namespace::TypeNS)
                }
                _ => Symbol::intern("debug_ty_name"),
            },
            Dependency::Item(_, _) => {
                let did = self.did().unwrap().0;
                match util::item_type(tcx, did) {
                    ItemType::Impl => tcx.item_name(tcx.trait_id_of_impl(did).unwrap()),
                    ItemType::Closure => Symbol::intern(&format!(
                        "closure{}",
                        tcx.def_path(did).data.last().unwrap().disambiguator
                    )),
                    ItemType::Field => {
                        let variant = tcx.parent(did);
                        let name = translate_accessor_name(
                            &tcx.item_name(variant).as_str(),
                            &tcx.item_name(did).as_str(),
                        );
                        Symbol::intern(&name)
                    }
                    _ => Symbol::intern(&value_name(tcx.item_name(did).as_str())),
                }
            }
            Dependency::Hacked(hacked_id, _, _) => match hacked_id {
                ExtendedId::PostconditionOnce => Symbol::intern("postcondition_once"),
                ExtendedId::PostconditionMut => Symbol::intern("postcondition_mut"),
                ExtendedId::Postcondition => Symbol::intern("postcondition"),
                ExtendedId::Precondition => Symbol::intern("precondition"),
                ExtendedId::Unnest => Symbol::intern("unnest"),
                ExtendedId::Resolve => Symbol::intern("resolve"),
                ExtendedId::Accessor(ix) => Symbol::intern(&format!("field_{ix}")),
            },
            Dependency::TyInv(..) => Symbol::intern("tyinv_should_not_appear"),
            Dependency::Builtin(_) => Symbol::intern("builtin_should_not_appear"),
            Dependency::StructuralResolve(_) => Symbol::intern("structural_resolve"),
        }
    }
}

fn resolve_item<'tcx>(
    item: DefId,
    substs: GenericArgsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Dependency<'tcx> {
    let resolved = if tcx.trait_of_item(item).is_some()
        && let Some(resolved) = traits::resolve_assoc_item_opt(tcx, param_env, item, substs)
    {
        resolved
    } else {
        // May happen:
        //    - if this is not a trait method, or
        //    - if we are resolving a type invariant
        (item, substs)
    };

    let (hacked_id, id, subst) = closure_hack(tcx, resolved.0, resolved.1);
    if let Some(hacked_id) = hacked_id {
        Dependency::Hacked(hacked_id, id, subst)
    } else if let Some(ty) = structural_resolve(tcx, resolved) {
        Dependency::StructuralResolve(ty)
    } else {
        Dependency::new(tcx, (id, subst))
    }
}

fn structural_resolve<'tcx>(
    tcx: TyCtxt<'tcx>,
    dep: (DefId, GenericArgsRef<'tcx>),
) -> Option<Ty<'tcx>> {
    if tcx.get_diagnostic_item(Symbol::intern("creusot_structural_resolve")).unwrap() == dep.0 {
        Some(dep.1.type_at(0))
    } else {
        None
    }
}

pub(crate) fn closure_hack<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> (Option<ExtendedId>, DefId, GenericArgsRef<'tcx>) {
    let hacked = if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id) {
        Some(ExtendedId::Precondition)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id) {
        Some(ExtendedId::PostconditionOnce)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id) {
        Some(ExtendedId::PostconditionMut)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id) {
        Some(ExtendedId::Postcondition)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_unnest"), def_id) {
        Some(ExtendedId::Unnest)
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id) {
        Some(ExtendedId::Resolve)
    } else {
        None
    };

    if hacked.is_some() {
        let self_ty = subst.types().nth(1).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (hacked, *id, csubst);
        }
    };

    if tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id) {
        let self_ty = subst.types().nth(0).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (Some(ExtendedId::Resolve), *id, csubst);
        }
    }

    (None, def_id, subst)
}
