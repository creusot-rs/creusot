use crate::prusti::ctx::{BaseCtx, InternedInfo};
use rustc_middle::ty::{
    AliasKind, Region, SubstsRef, Ty, TyCtxt, TyKind, TypeFoldable, TypeFolder, TypeSuperFoldable,
};
use rustc_span::{def_id::DefId, Symbol};

#[derive(Copy, Clone, Eq, PartialEq)]
pub(super) enum StaticNormalizationState {
    Normal,
    Static,
}

pub struct StaticNormalizerDefIds {
    user: DefId,
    internal: DefId,
}

impl StaticNormalizerDefIds {
    pub fn new(tcx: TyCtxt<'_>) -> StaticNormalizerDefIds {
        let map = &tcx.all_diagnostic_items(()).name_to_id;
        let find_did = |name| map[&Symbol::intern(name)];
        StaticNormalizerDefIds {
            user: find_did("prusti_replace_static_user"),
            internal: find_did("prusti_replace_lft"),
        }
    }

    pub(super) fn ty_as_replace_lft_adt<'tcx>(
        &self,
        ty: Ty<'tcx>,
    ) -> Option<(Region<'tcx>, Ty<'tcx>)> {
        match ty.kind() {
            TyKind::Adt(def, subst) if def.did() == self.internal => {
                let subst: SubstsRef = subst;
                let mut iter = subst.iter();
                let r = iter.next().unwrap().expect_region();
                let ty = iter.next().unwrap().expect_ty();
                Some((r, ty))
            }
            _ => None,
        }
    }
}

#[derive(Copy, Clone)]
struct StaticNormalizer<'a, 'tcx> {
    state: StaticNormalizationState,
    ctx: &'a BaseCtx<'a, 'tcx>,
    static_r: Region<'tcx>,
}

impl<'a, 'tcx> TypeFolder<TyCtxt<'tcx>> for StaticNormalizer<'a, 'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        match t.kind() {
            TyKind::Alias(AliasKind::Projection, x)
                if x.def_id == self.ctx.static_replacer_info.user =>
            {
                let ty = x.substs.types().next().unwrap();
                StaticNormalizer { state: StaticNormalizationState::Static, ..*self }.fold_ty(ty)
            }
            _ => t.super_fold_with(self),
        }
    }

    fn fold_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        match self.state {
            StaticNormalizationState::Normal => r,
            StaticNormalizationState::Static => self.static_r,
        }
    }
}

pub(super) fn normalize_static_replacer<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    ctx: &BaseCtx<'_, 'tcx>,
    ty: T,
    static_r: Region<'tcx>,
) -> T {
    let mut n = StaticNormalizer { ctx, state: StaticNormalizationState::Normal, static_r };
    ty.fold_with(&mut n)
}

pub(super) struct FixingRegionReplacer<'a, 'tcx, F: FnMut(Region<'tcx>) -> Region<'tcx>> {
    pub ctx: &'a InternedInfo<'tcx>,
    pub f: F,
}

impl<'a, 'tcx, F: FnMut(Region<'tcx>) -> Region<'tcx>> TypeFolder<TyCtxt<'tcx>>
    for FixingRegionReplacer<'a, 'tcx, F>
{
    fn interner(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }

    // fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
    //     match t.kind() {
    //         TyKind::Param(..) => {
    //             let r = self.ctx.curr_region();
    //             let did = self.ctx.static_replacer_info.internal;
    //             let tcx = self.ctx.tcx;
    //             tcx.mk_adt(tcx.adt_def(did), tcx.mk_substs(&[r.into(), t.into()]))
    //         }
    //         _ => t.super_fold_with(self),
    //     }
    // }

    fn fold_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        (self.f)(r)
    }
}

pub(super) struct PrettyRegionReplacer<'a, 'tcx, F: FnMut(Region<'tcx>) -> Region<'tcx>> {
    pub ctx: &'a InternedInfo<'tcx>,
    pub f: F,
}

impl<'a, 'tcx, F: FnMut(Region<'tcx>) -> Region<'tcx>> TypeFolder<TyCtxt<'tcx>>
    for PrettyRegionReplacer<'a, 'tcx, F>
{
    fn interner(&self) -> TyCtxt<'tcx> {
        self.ctx.tcx
    }

    fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
        let ctx = self.ctx;
        if let Some((r, inner)) = ctx.static_replacer_info.ty_as_replace_lft_adt(t) {
            let r = (self.f)(r);
            if r.is_erased() || r.get_name() == Some(ctx.curr_sym) {
                inner
            } else if r.is_static() {
                ctx.tcx.mk_alias(
                    AliasKind::Projection,
                    ctx.tcx.mk_alias_ty(
                        ctx.static_replacer_info.user,
                        ctx.tcx.mk_substs(&[inner.into()]),
                    ),
                )
            } else {
                t.super_fold_with(self)
            }
        } else {
            t.super_fold_with(self)
        }
    }

    fn fold_region(&mut self, r: Region<'tcx>) -> Region<'tcx> {
        (self.f)(r)
    }
}
