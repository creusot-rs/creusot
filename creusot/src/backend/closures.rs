use crate::{
    contracts_items::Intrinsic,
    ctx::*,
    naming::name,
    translation::{
        pearlite::{
            Ident, Pattern, Term, TermKind, TermVisitorMut, normalize, super_visit_mut_term,
        },
        specification::{PreSignature, contract_of},
    },
};
use indexmap::IndexMap;
use itertools::Itertools;
use rustc_abi::FieldIdx;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir_typeck::expr_use_visitor::PlaceBase;
use rustc_middle::{
    mir::Mutability,
    ty::{
        BorrowKind, CapturedPlace, ClosureKind, GenericArg, GenericArgsRef, Ty, TyKind, TypingEnv,
        UpvarCapture,
    },
};
use std::{assert_matches::assert_matches, collections::HashSet, iter::once};

fn closure_captures<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: LocalDefId,
) -> impl Iterator<Item = ((FieldIdx, &'tcx CapturedPlace<'tcx>), Ty<'tcx>)> {
    let TyKind::Closure(_, subst) = ctx.type_of(def_id).instantiate_identity().kind() else {
        unreachable!()
    };

    (0usize..)
        .map(|ix| -> FieldIdx { ix.into() })
        .zip(ctx.closure_captures(def_id).iter().copied())
        .zip_eq(subst.as_closure().upvar_tys())
}

pub(crate) fn closure_hist_inv<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: LocalDefId,
    self_: Term<'tcx>,
    future: Term<'tcx>,
) -> Term<'tcx> {
    let TyKind::Closure(_, subst) = ctx.type_of(def_id).instantiate_identity().kind() else {
        unreachable!()
    };
    let closure_kind = subst.as_closure().kind();
    assert!(closure_kind.extends(ClosureKind::FnMut));

    if closure_kind == ClosureKind::Fn {
        // Make sure `fn_hist_inv` holds
        return self_.clone().eq(ctx.tcx, future);
    }

    let span = ctx.def_span(def_id);
    let mut hist_inv = Term::true_(ctx.tcx);
    for ((f, capture), ty) in closure_captures(ctx, def_id) {
        match capture.info.capture_kind {
            // if we captured by value we get no hist_inving predicate
            UpvarCapture::ByValue => continue,
            UpvarCapture::ByRef(is_mut) => {
                let hist_inv_one = if is_mut == BorrowKind::Immutable {
                    future.clone().proj(f, ty).eq(ctx.tcx, self_.clone().proj(f, ty))
                } else {
                    future.clone().proj(f, ty).fin().eq(ctx.tcx, self_.clone().proj(f, ty).fin())
                };

                hist_inv = hist_inv.conj(hist_inv_one);
            }
            UpvarCapture::ByUse => ctx.crash_and_error(span, "ByUse capture kind is not supported"),
        }
    }

    normalize(ctx, ctx.typing_env(def_id.into()), hist_inv).span(span)
}

pub(crate) fn closure_pre<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: LocalDefId,
    self_: Term<'tcx>,
    args: Term<'tcx>,
) -> Term<'tcx> {
    let TyKind::Closure(_, subst) = ctx.type_of(def_id).instantiate_identity().kind() else {
        unreachable!()
    };
    let closure_kind = subst.as_closure().kind();
    let PreSignature { contract, inputs, output: _ } = contract_of(ctx, def_id.into());

    let mut pre;
    if contract.has_user_contract {
        pre = contract.requires_conj(ctx.tcx);
        ClosSubst::pre(ctx, def_id, self_).visit_mut_term(&mut pre);
    } else {
        let arg_vars = inputs[1..].iter().map(|&(nm, _, ty)| Term::var(nm, ty));
        let self_arg;
        let mut k = None;

        match closure_kind {
            ClosureKind::Fn => self_arg = self_.shr_ref(ctx.tcx),
            ClosureKind::FnMut => {
                let bor_self_ident = Ident::fresh_local("bor_self");
                let bor_self_ty =
                    Ty::new_ref(ctx.tcx, ctx.lifetimes.re_erased, self_.ty, Mutability::Mut);
                let bor_self = Term::var(bor_self_ident, bor_self_ty);
                self_arg = bor_self.clone();
                k = Some(move |t| {
                    (bor_self.cur().eq(ctx.tcx, self_))
                        .implies(t)
                        .forall((bor_self_ident.into(), bor_self_ty))
                });
            }
            ClosureKind::FnOnce => self_arg = self_,
        }

        let params = once(self_arg).chain(arg_vars.clone()).collect();
        pre = Term {
            kind: TermKind::Precondition { item: def_id.into(), subst, params },
            ty: ctx.types.bool,
            span: ctx.def_span(def_id),
        };
        if let Some(k) = k {
            pre = k(pre)
        }
    }

    if inputs.len() > 1 {
        let pattern = Pattern::tuple(
            inputs[1..].iter().map(|&(nm, span, ty)| Pattern::binder_sp(nm, span, ty)),
            args.ty,
        );
        pre = Term::let_(pattern, args, pre).span(ctx.def_span(def_id));
    }

    normalize(ctx, ctx.typing_env(def_id.into()), pre)
}

pub(crate) fn closure_post<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    target_kind: ClosureKind,
    def_id: LocalDefId,
    self_: Term<'tcx>,
    args: Term<'tcx>,
    result_state: Option<Term<'tcx>>,
) -> Term<'tcx> {
    let TyKind::Closure(_, subst) = ctx.type_of(def_id).instantiate_identity().kind() else {
        unreachable!()
    };
    let closure_kind = subst.as_closure().kind();
    let PreSignature { contract, inputs, output } = contract_of(ctx, def_id.into());

    let to_resolve;
    let mut post;
    if contract.has_user_contract {
        post = contract.ensures_conj(ctx.tcx);
        match target_kind {
            ClosureKind::Fn => {
                to_resolve = vec![];
                ClosSubst::post_ref(ctx, def_id, self_.clone(), self_).visit_mut_term(&mut post);
            }
            ClosureKind::FnMut => {
                to_resolve = vec![];
                let result_state = result_state.unwrap();
                ClosSubst::post_ref(ctx, def_id, self_.clone(), result_state.clone())
                    .visit_mut_term(&mut post);
                let hist_inv = Term::call_no_normalize(
                    ctx.tcx,
                    Intrinsic::HistInv.get(ctx),
                    ctx.mk_args(&[args.ty, self_.ty].map(GenericArg::from)),
                    [self_, result_state],
                );
                // Thanks to that, `postcondition_mut_hist_inv` and `fn_mut` are satisfied
                // Note that we do not include it in the `target_kind == FnOnce` case, because hist_inv
                // is actually already included and combined with resolution when `ClosSubst::post_owned`
                // substitutes the post state of &(resp. mut)-captured variables by the final value
                // (resp. value).
                post = post.conj(hist_inv);
            }
            ClosureKind::FnOnce => {
                let post_projs: Vec<Option<Term>>;
                match closure_kind {
                    ClosureKind::FnOnce => {
                        // If this is an FnOnce closure, then variables captured by value
                        // are consumed by the closure, and thus we cannot refer to them in
                        // the post state.
                        post_projs = vec![None; closure_captures(ctx, def_id).count()];
                        to_resolve = vec![]
                    }
                    ClosureKind::Fn => {
                        post_projs = closure_captures(ctx, def_id)
                            .map(|((f, capture), ty)| {
                                (capture.info.capture_kind == UpvarCapture::ByValue)
                                    .then(|| self_.clone().proj(f, ty))
                            })
                            .collect();
                        to_resolve = post_projs.iter().filter_map(Clone::clone).collect();
                    }
                    ClosureKind::FnMut => {
                        post_projs = closure_captures(ctx, def_id)
                            .map(|((_, capture), ty)| {
                                (capture.info.capture_kind == UpvarCapture::ByValue)
                                    .then(|| Term::var(Ident::fresh_local("x"), ty))
                            })
                            .collect();
                        to_resolve = post_projs.iter().filter_map(Clone::clone).collect();
                    }
                };
                ClosSubst::post_owned(ctx, def_id, self_, post_projs).visit_mut_term(&mut post);
            }
        }
    } else {
        let arg_vars = inputs[1..].iter().map(|&(nm, _, ty)| Term::var(nm, ty));
        let result = Term::var(name::result(), output);
        match closure_kind {
            ClosureKind::Fn => {
                let bor_self = self_.clone().shr_ref(ctx.tcx);
                let params = once(bor_self).chain(arg_vars.clone()).chain([result]).collect();
                post = Term {
                    kind: TermKind::Postcondition { item: def_id.into(), subst, params },
                    ty: ctx.types.bool,
                    span: ctx.def_span(def_id),
                };
                to_resolve =
                    if target_kind == ClosureKind::FnOnce { vec![self_.clone()] } else { vec![] };
                if target_kind == ClosureKind::FnMut {
                    post = post.conj(self_.clone().eq(ctx.tcx, result_state.unwrap()))
                }
            }
            ClosureKind::FnMut => {
                let bor_self_ident = Ident::fresh_local("bor_self");
                let bor_self_ty =
                    Ty::new_ref(ctx.tcx, ctx.lifetimes.re_erased, self_.ty, Mutability::Mut);
                let bor_self = Term::var(bor_self_ident, bor_self_ty);
                let params =
                    once(bor_self.clone()).chain(arg_vars.clone()).chain([result]).collect();
                post = Term {
                    kind: TermKind::Postcondition { item: def_id.into(), subst, params },
                    ty: ctx.types.bool,
                    span: ctx.def_span(def_id),
                };

                let result_state = match target_kind {
                    ClosureKind::FnMut => {
                        to_resolve = vec![];
                        result_state.unwrap().clone()
                    }
                    ClosureKind::FnOnce => {
                        let r = Term::var(Ident::fresh_local("e"), self_.ty);
                        to_resolve = vec![r.clone()];
                        r
                    }
                    ClosureKind::Fn => unreachable!(),
                };

                // Thanks to that, `postcondition_mut_hist_inv` and `fn_mut` are satisfied
                let hist_inv = Term::call_no_normalize(
                    ctx.tcx,
                    Intrinsic::HistInv.get(ctx),
                    ctx.mk_args(&[args.ty, self_.ty].map(GenericArg::from)),
                    [self_.clone(), result_state.clone()],
                );

                post = Term::true_(ctx.tcx)
                    .conj(bor_self.clone().cur().eq(ctx.tcx, self_))
                    .conj(bor_self.fin().eq(ctx.tcx, result_state))
                    .conj(post)
                    .conj(hist_inv)
                    .exists((bor_self_ident.into(), bor_self_ty))
            }
            ClosureKind::FnOnce => {
                assert_eq!(target_kind, ClosureKind::FnOnce);
                let params = once(self_.clone()).chain(arg_vars.clone()).chain([result]).collect();
                to_resolve = vec![];
                post = Term {
                    kind: TermKind::Postcondition { item: def_id.into(), subst, params },
                    ty: ctx.types.bool,
                    span: ctx.def_span(def_id),
                }
            }
        }
    }

    let typing_env = ctx.typing_env(def_id.into());

    // Make sure fn_once and fn_mut_once are satisfied
    post = to_resolve.iter().fold(post, |p, r| {
        if let Some((id, subst)) = ctx.resolve(typing_env, r.ty) {
            p.conj(Term::call_no_normalize(ctx.tcx, id, subst, [r.clone()]))
        } else {
            p
        }
    });
    if closure_kind == ClosureKind::FnMut {
        post = to_resolve.iter().rfold(post, |p, r| {
            let TermKind::Var(sym) = r.kind else { unreachable!() };
            p.exists((sym, r.ty))
        });
    }

    if inputs.len() > 1 {
        let pattern = Pattern::tuple(
            inputs[1..].iter().map(|&(nm, span, ty)| Pattern::binder_sp(nm, span, ty)),
            args.ty,
        );
        post = Term::let_(pattern, args, post).span(ctx.def_span(def_id));
    }

    normalize(ctx, typing_env, post)
}

pub(crate) fn closure_resolve<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Term<'tcx> {
    assert! {bound.len() == 1};
    let mut resolve = Term::true_(ctx.tcx);
    let self_ = Term::var(bound[0], ctx.type_of(def_id).instantiate_identity());
    let csubst = subst.as_closure();
    let typing_env = TypingEnv::non_body_analysis(ctx.tcx, def_id);
    for (ix, ty) in csubst.upvar_tys().iter().enumerate() {
        if let Some((id, subst)) = ctx.resolve(typing_env, ty) {
            let proj = self_.clone().proj(ix.into(), ty);
            resolve = Term::call(ctx.tcx, typing_env, id, subst, [proj]).conj(resolve);
        }
    }
    resolve
}

// Responsible for replacing occurences of captured variables with projections from the closure environment.
// Must also account for the *kind* of capture and the *kind* of closure involved each time.
pub(crate) struct ClosSubst<'tcx, 'a> {
    ctx: &'a TranslationCtx<'tcx>,
    map_cur: IndexMap<Ident, Option<Term<'tcx>>>,
    map_old: IndexMap<Ident, Term<'tcx>>,
    bound: HashSet<Ident>,
}

impl<'tcx> TermVisitorMut<'tcx> for ClosSubst<'tcx, '_> {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        match &mut term.kind {
            TermKind::Old { term: box Term { kind: TermKind::Var(x), .. }, .. }
                if !self.bound.contains(&x.0)
                    && let Some(v) = self.map_old.get(&x.0) =>
            {
                *term = v.clone();
            }
            TermKind::Old { .. } => self.ctx.crash_and_error(
                term.span,
                "`old` should only be used in post-conditions of closures for captured variables.",
            ),
            TermKind::Var(x)
                if !self.bound.contains(&x.0)
                    && let Some(v) = self.map_cur.get(&x.0) =>
            {
                if let Some(v) = v {
                    *term = v.clone();
                } else {
                    self.ctx.fatal_error(
                        term.span,
                        "Use of a closure capture in a post-condition, but it is consumed by the closure.",
                    ).emit()
                }
            }
            TermKind::Quant { binder, .. } => {
                let mut bound = self.bound.clone();
                for (ident, _) in binder {
                    bound.insert(ident.0);
                }
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Match { arms, .. } => {
                let mut bound = self.bound.clone();
                arms.iter().for_each(|arm| arm.0.binds(&mut bound));
                std::mem::swap(&mut self.bound, &mut bound);
                super_visit_mut_term(term, self);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Let { pattern, box arg, box body } => {
                self.visit_mut_term(arg);
                let mut bound = self.bound.clone();
                pattern.binds(&mut bound);
                std::mem::swap(&mut self.bound, &mut bound);
                self.visit_mut_term(body);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            TermKind::Closure { bound: bound_new, box body } => {
                let mut bound = self.bound.clone();
                bound.extend(bound_new.iter().map(|b| b.0.0));
                std::mem::swap(&mut self.bound, &mut bound);
                self.visit_mut_term(body);
                std::mem::swap(&mut self.bound, &mut bound);
            }
            _ => super_visit_mut_term(term, self),
        }
    }
}

impl<'tcx, 'a> ClosSubst<'tcx, 'a> {
    pub(crate) fn pre(
        ctx: &'a TranslationCtx<'tcx>,
        def_id: LocalDefId,
        self_pre: Term<'tcx>,
    ) -> Self {
        let map_cur = closure_captures(ctx, def_id)
            .map(|((f, cap), ty)| {
                let span = cap.get_path_span(ctx.tcx);
                if !cap.place.projections.is_empty() {
                    ctx.dcx().span_bug(
                        span,
                        format!("This specification captures a structure field. This is currently not supported by Creusot (see Issue #1538). The workaround is to use Rust edition 2018."),
                    )
                }
                let proj = self_pre.clone().proj(f, ty).span(span);
                let term = match cap.info.capture_kind {
                    UpvarCapture::ByValue => proj,
                    UpvarCapture::ByRef(BorrowKind::Mutable | BorrowKind::UniqueImmutable) => {
                        proj.cur()
                    }
                    UpvarCapture::ByRef(BorrowKind::Immutable) => proj.shr_deref(),
                    UpvarCapture::ByUse => ctx.crash_and_error(span, "ByUse capture kind is not supported"),
                };
                let hir_id = match cap.place.base {
                    PlaceBase::Rvalue | PlaceBase::StaticItem => ctx.dcx().span_bug(
                        span,
                        format!("Unexpected place in closure capture: {:?}", cap.place.base),
                    ),
                    PlaceBase::Local(hir_id) => hir_id,
                    PlaceBase::Upvar(upvar_id) => upvar_id.var_path.hir_id,
                };
                (ctx.rename(hir_id), Some(term))
            })
            .collect();
        ClosSubst { ctx, map_cur, map_old: Default::default(), bound: Default::default() }
    }

    pub(crate) fn post_ref(
        ctx: &'a TranslationCtx<'tcx>,
        def_id: LocalDefId,
        self_pre: Term<'tcx>,
        self_post: Term<'tcx>,
    ) -> Self {
        let (map_old, map_cur) = closure_captures(ctx, def_id)
            .map(|((f, cap), ty)| {
                assert!(cap.place.projections.is_empty());
                let span = cap.get_path_span(ctx.tcx);
                let proj_pre = self_pre.clone().proj(f, ty).span(span);
                let proj_post = self_post.clone().proj(f, ty).span(span);
                let (term_pre, term_post) = match cap.info.capture_kind {
                    UpvarCapture::ByValue => (proj_pre, proj_post),
                    UpvarCapture::ByRef(BorrowKind::Mutable | BorrowKind::UniqueImmutable) => {
                        (proj_pre.cur(), proj_post.cur())
                    }
                    UpvarCapture::ByRef(BorrowKind::Immutable) => {
                        (proj_pre.shr_deref(), proj_post.shr_deref())
                    }
                    UpvarCapture::ByUse => {
                        ctx.crash_and_error(span, "ByUse capture kind is not supported")
                    }
                };
                let hir_id = match cap.place.base {
                    PlaceBase::Rvalue | PlaceBase::StaticItem => ctx.dcx().span_bug(
                        span,
                        format!("Unexpected place in closure capture: {:?}", cap.place.base),
                    ),
                    PlaceBase::Local(hir_id) => hir_id,
                    PlaceBase::Upvar(upvar_id) => upvar_id.var_path.hir_id,
                };
                let nm = ctx.rename(hir_id);
                ((nm, term_pre), (nm, Some(term_post)))
            })
            .unzip();
        ClosSubst { ctx, map_cur, map_old, bound: Default::default() }
    }

    pub(crate) fn post_owned(
        ctx: &'a TranslationCtx<'tcx>,
        def_id: LocalDefId,
        self_: Term<'tcx>,
        post_owned_projs: impl IntoIterator<Item = Option<Term<'tcx>>>,
    ) -> Self {
        let (map_old, map_cur) = closure_captures(ctx, def_id)
            .zip(post_owned_projs)
            .map(|(((f, cap), ty), post_owned_proj)| {
                assert!(cap.place.projections.is_empty());
                let span = cap.get_path_span(ctx.tcx);
                let proj = self_.clone().proj(f, ty).span(span);
                let (term_pre, term_post) = match cap.info.capture_kind {
                    UpvarCapture::ByValue => (proj, post_owned_proj),
                    UpvarCapture::ByRef(BorrowKind::Mutable | BorrowKind::UniqueImmutable) => {
                        assert_matches!(post_owned_proj, None);
                        (proj.clone().cur(), Some(proj.fin()))
                    }
                    UpvarCapture::ByRef(BorrowKind::Immutable) => {
                        assert_matches!(post_owned_proj, None);
                        (proj.clone().shr_deref(), Some(proj.shr_deref()))
                    }
                    UpvarCapture::ByUse => {
                        ctx.crash_and_error(span, "ByUse capture kind is not supported")
                    }
                };
                let hir_id = match cap.place.base {
                    PlaceBase::Rvalue | PlaceBase::StaticItem => ctx.dcx().span_bug(
                        span,
                        format!("Unexpected place in closure capture: {:?}", cap.place.base),
                    ),
                    PlaceBase::Local(hir_id) => hir_id,
                    PlaceBase::Upvar(upvar_id) => upvar_id.var_path.hir_id,
                };
                let nm = ctx.rename(hir_id);
                ((nm, term_pre), (nm, term_post))
            })
            .unzip();
        ClosSubst { ctx, map_cur, map_old, bound: Default::default() }
    }
}
