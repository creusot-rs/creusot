use indexmap::IndexSet;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{EarlyBinder, InternalSubsts, ParamEnv, SubstsRef, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_type_ir::AliasKind;

use crate::{
    ctx::TranslationCtx,
    translation::{
        pearlite::{super_visit_term, Pattern, Term, TermVisitor},
        specification::PreContract,
        traits,
    },
    util::{self, ItemType, PreSignature},
};

use super::{ty_inv::TyInvKind, walk_types, PreludeModule, TransId, Why3Generator};

/// Dependencies between items and the resolution logic to find the 'monomorphic' forms accounting
/// for various Creusot hacks like the handling of closures.
///
/// These should be used both to power the cloning system and to order the overall translation of items in Creusot.
///

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord, TypeVisitable, TypeFoldable)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item(DefId, SubstsRef<'tcx>),
    TyInv(Ty<'tcx>, TyInvKind),
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, (did, subst): (DefId, SubstsRef<'tcx>)) -> Self {
        match util::item_type(tcx, did) {
            ItemType::Type => Dependency::Type(tcx.mk_adt(tcx.adt_def(did), subst)),
            ItemType::AssocTy => Dependency::Type(tcx.mk_projection(did, subst)),
            _ => Dependency::Item(did, subst),
        }
    }

    pub(crate) fn from_trans_id(tcx: TyCtxt<'tcx>, trans_id: TransId) -> Self {
        match trans_id {
            TransId::Item(self_id) => {
                let subst = match tcx.def_kind(self_id) {
                    DefKind::Closure => match tcx.type_of(self_id).subst_identity().kind() {
                        TyKind::Closure(_, subst) => subst,
                        _ => unreachable!(),
                    },
                    _ => InternalSubsts::identity_for_item(tcx, self_id),
                };

                Dependency::new(tcx, (self_id, subst)).erase_regions(tcx)
            }
            TransId::TyInv(inv_kind) => Dependency::TyInv(inv_kind.to_skeleton_ty(tcx), inv_kind),
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

    pub(crate) fn did(self) -> Option<(DefId, SubstsRef<'tcx>)> {
        match self {
            Dependency::Item(def_id, subst) => Some((def_id, subst)),
            Dependency::Type(t) | Dependency::TyInv(t, _) => match t.kind() {
                TyKind::Adt(def, substs) => Some((def.did(), substs)),
                TyKind::Closure(id, substs) => Some((*id, substs)),
                TyKind::Alias(AliasKind::Projection, aty) => Some((aty.def_id, aty.substs)),
                _ => None,
            },
        }
    }

    pub(crate) fn is_inv(&self) -> bool {
        matches!(self, Dependency::TyInv(_, _))
    }

    #[inline]
    pub(crate) fn erase_regions(self, tcx: TyCtxt<'tcx>) -> Self {
        tcx.erase_regions(self)
    }

    #[inline]
    pub(crate) fn subst(self, tcx: TyCtxt<'tcx>, other: Dependency<'tcx>) -> Self {
        let substs = if let Dependency::TyInv(ty, inv_kind) = other {
            inv_kind.tyinv_substs(tcx, ty)
        } else if let Some((_, substs)) = other.did() {
            substs
        } else {
            return self;
        };

        EarlyBinder::bind(self).subst(tcx, substs)
    }

    #[inline]
    pub(crate) fn closure_hack(self, tcx: TyCtxt<'tcx>) -> Self {
        match self {
            Dependency::Item(did, subst) => Dependency::new(tcx, closure_hack(tcx, did, subst)),
            _ => self,
        }
    }
}

fn resolve_item<'tcx>(
    item: DefId,
    substs: SubstsRef<'tcx>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
) -> Dependency<'tcx> {
    let resolved = if tcx.trait_of_item(item).is_some()
        && let Some(resolved) = traits::resolve_opt(tcx, param_env, item, substs) {
            resolved
    } else {
        (item, substs)
    };

    let resolved = closure_hack(tcx, resolved.0, resolved.1);
    Dependency::new(tcx, resolved)
}

pub(crate) fn closure_hack<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> (DefId, SubstsRef<'tcx>) {
    if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_unnest"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id)
    {
        let self_ty = subst.types().nth(1).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (*id, csubst);
        }
    };

    if tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
    {
        let self_ty = subst.types().nth(0).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return (*id, csubst);
        }
    }

    (def_id, subst)
}

pub(crate) struct Dependencies<'a, 'tcx>(
    pub &'a mut Why3Generator<'tcx>,
    pub IndexSet<Dependency<'tcx>>,
    pub IndexSet<PreludeModule>,
);
impl<'a, 'tcx> Dependencies<'a, 'tcx> {
    fn push(&mut self, def_id: DefId, substs: SubstsRef<'tcx>) {
        self.1.insert(Dependency::new(self.0.tcx, (def_id, substs)));
        substs.gather_deps(self);
    }
    fn push_prelude(&mut self, pm: PreludeModule) {
        self.2.insert(pm);
    }
}

pub(crate) trait HasDeps<'tcx> {
    fn gather_deps(&self, deps: &mut Dependencies<'_, 'tcx>);
}

impl<'tcx> HasDeps<'tcx> for Term<'tcx> {
    fn gather_deps(&self, deps: &mut Dependencies<'_, 'tcx>) {
        deps.visit_term(self);
    }
}

impl<'tcx> HasDeps<'tcx> for PreSignature<'tcx> {
    fn gather_deps(&self, deps: &mut Dependencies<'_, 'tcx>) {
        self.inputs.iter().for_each(|(_, _, ty)| ty.gather_deps(deps));
        self.output.gather_deps(deps);
        self.contract.gather_deps(deps);
    }
}

impl<'tcx> HasDeps<'tcx> for PreContract<'tcx> {
    fn gather_deps(&self, deps: &mut Dependencies<'_, 'tcx>) {
        self.variant.iter().for_each(|t| t.gather_deps(deps));
        self.requires.iter().for_each(|t| t.gather_deps(deps));
        self.ensures.iter().for_each(|t| t.gather_deps(deps));
    }
}

impl<'tcx> HasDeps<'tcx> for Ty<'tcx> {
    fn gather_deps(&self, deps: &mut Dependencies<'_, 'tcx>) {
        walk_types(*self, |ty| {
            use rustc_type_ir::TyKind;
            match ty.kind() {
                TyKind::Adt(def, subst) => {
                    deps.push(def.did(), subst);
                    for p in deps.0.projections_in_ty(def.did()).to_owned() {
                        EarlyBinder::bind(p.to_ty(deps.0.tcx))
                            .subst(deps.0.tcx, subst)
                            .gather_deps(deps);
                    }
                }
                TyKind::Alias(_, aty) => deps.push(aty.def_id, aty.substs),
                _ => (),
            }
        })
    }
}

impl<'tcx> HasDeps<'tcx> for SubstsRef<'tcx> {
    fn gather_deps(&self, deps: &mut Dependencies<'_, 'tcx>) {
        walk_types(*self, |ty| {
            ty.gather_deps(deps);
        })
    }
}

impl<'tcx> HasDeps<'tcx> for Pattern<'tcx> {
    fn gather_deps(&self, deps: &mut Dependencies<'_, 'tcx>) {
        match self {
            Pattern::Constructor { adt, substs, fields, .. } => {
                let type_id = match deps.0.def_kind(*adt) {
                    DefKind::Closure | DefKind::Struct | DefKind::Enum | DefKind::Union => *adt,
                    DefKind::Variant => deps.0.parent(*adt),
                    _ => unreachable!("Not a type or constructor"),
                };
                deps.push(type_id, substs);
                fields.iter().for_each(|p| p.gather_deps(deps))
            }
            Pattern::Tuple(_) => (),
            Pattern::Wildcard => (),
            Pattern::Binder(_) => (),
            Pattern::Boolean(_) => (),
        }
    }
}

impl<'tcx> TermVisitor<'tcx> for Dependencies<'_, 'tcx> {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        use crate::translation::pearlite::TermKind;
        // TODO: This is missing dependencies that occur inside of patterns and in types
        match &term.kind {
            TermKind::Item(id, subst) => self.push(*id, subst),
            TermKind::Call { id, subst, .. } => self.push(*id, subst),
            TermKind::Constructor { typ, variant, .. } => {
                let TyKind::Adt(_, subst) = term.ty.kind() else { return };
                let def_id = self.0.adt_def(typ).variants()[*variant].def_id;
                self.push(self.0.adt_def(typ).did(), subst);
                self.push(def_id, subst);
            }
            TermKind::Match { scrutinee, arms } => {
                scrutinee.ty.gather_deps(self);

                arms.iter().for_each(|(pat, _)| pat.gather_deps(self));
            }
            TermKind::Cur { .. } => self.push_prelude(PreludeModule::Borrow),
            TermKind::Fin { .. } => self.push_prelude(PreludeModule::Borrow),
            TermKind::Forall { binder, .. } => binder.1.gather_deps(self),
            TermKind::Exists { binder, .. } => binder.1.gather_deps(self),
            TermKind::Projection { lhs, .. } => {
                let base_ty = lhs.ty;

                let (def_id, substs) = match base_ty.kind() {
                    TyKind::Closure(did, substs) => (*did, substs),
                    TyKind::Adt(def, substs) => (def.did(), substs),
                    _ => unreachable!(),
                };
                self.push(def_id, substs);
            }
            _ => {}
        };
        super_visit_term(term, self)
    }
}
