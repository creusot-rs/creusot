use crate::{
    backend::is_trusted_item,
    contracts_items::{Intrinsic, is_logic, is_no_translate},
    ctx::TranslationCtx,
    lints::{Diagnostics, UNCHECKED_UNSAFE},
    naming::name,
};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;

pub fn validate_safety(ctx: &TranslationCtx) {
    for local_id in ctx.hir_body_owners() {
        let def_id = local_id.to_def_id();
        if is_no_translate(ctx.tcx, def_id)
            || is_logic(ctx.tcx, def_id)
            || is_trusted_item(ctx.tcx, def_id)
        {
            continue;
        }
        safety_check(ctx, def_id);
    }
}

/// If this function has safety obligations (a safe function containing unsafe blocks),
/// check that its preconditions are trivial in `nopanic` mode,
/// of the form `mode!().nopanic() ==> _`.
fn safety_check(ctx: &TranslationCtx, def_id: DefId) {
    if matches!(ctx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
        && is_safe(ctx.tcx, def_id)
        && has_nonghost_unsafe_block(ctx.tcx, def_id)
    {
        let sig = ctx.sig(def_id);
        for pre in &sig.contract.requires {
            use crate::translation::pearlite::{Literal::Bool, TermKind::*};
            if let Impl { lhs: ref arg, .. } = pre.term.kind
                && let Call { id, ref args, .. } = arg.kind
                && Intrinsic::ModeNoPanic.is(ctx, id)
                && let Var(v) = args[0].kind
                && v.0 == name::mode()
            {
                continue;
            }
            if let Lit(Bool(true)) = pre.term.kind {
                continue;
            }
            // Warn for now
            ctx.tcx.emit_node_span_lint(
                UNCHECKED_UNSAFE,
                rustc_hir::HirId::make_owner(def_id.expect_local()),
                pre.term.span,
                Diagnostics::UncheckedUnsafe,
            );
            break;
        }
    }
}

fn is_safe(tcx: TyCtxt, def_id: DefId) -> bool {
    tcx.fn_sig(def_id).skip_binder().skip_binder().safety().is_safe()
}

// Don't warn about unsafe blocks in ghost blocks.
fn has_nonghost_unsafe_block(tcx: TyCtxt, def_id: DefId) -> bool {
    use rustc_hir::{
        self as hir,
        intravisit::{Visitor, walk_block, walk_expr},
    };
    use rustc_middle::hir::nested_filter::OnlyBodies;
    use std::ops::ControlFlow;
    struct HasUnsafeBlock<'tcx>(TyCtxt<'tcx>);
    impl<'tcx> Visitor<'tcx> for HasUnsafeBlock<'tcx> {
        type NestedFilter = OnlyBodies;
        type Result = ControlFlow<()>;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.0
        }

        fn visit_block(&mut self, b: &'tcx hir::Block<'tcx>) -> Self::Result {
            use rustc_hir::UnsafeSource::UserProvided;
            if let hir::BlockCheckMode::UnsafeBlock(UserProvided) = b.rules {
                return ControlFlow::Break(());
            }
            walk_block(self, b)
        }

        fn visit_expr(&mut self, e: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Block(..) = e.kind
                && crate::validate::is_ghost_block(self.0, e.hir_id)
            {
                return ControlFlow::Continue(());
            }
            walk_expr(self, e)
        }
    }
    HasUnsafeBlock(tcx).visit_body(tcx.hir_body_owned_by(def_id.expect_local())).is_break()
}
