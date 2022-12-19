use crate::{
    backend::program::uint_from_int,
    ctx::TranslationCtx,
    error::Error,
    translation::{
        binop_to_binop, constant::from_mir_constant, fmir, function::LocalIdent, unop_to_unop,
    },
    util::{self, constructor_qname},
};
use creusot_rustc::{
    hir::def_id::DefId,
    middle::{mir::TerminatorKind, ty::ParamEnv},
    smir::mir::{Body, BorrowKind, Operand, Promoted, StatementKind},
};
use why3::{
    declaration::{Contract, Decl, LetDecl, LetKind, Signature},
    exp::{Binder, Exp, Pattern},
    QName,
};

use crate::error::CreusotResult;

use super::{place::translate_rplace_inner, BodyTranslator};

// pub(crate) fn promoted_signature<'tcx>(
//     ctx: &mut TranslationCtx<'tcx>,
//     names: &mut CloneMap<'tcx>,
//     (promoted, body): (Promoted, &Body<'tcx>),
// ) -> Signature {
//     let args = body
//         .args_iter()
//         .map(|arg| {
//             let info = &body.local_decls[arg];
//             let ty = translate_ty(ctx, names, info.source_info.span, info.ty);
//             Binder::typed(LocalIdent::anon(arg).ident(), ty)
//         })
//         .collect();
//     let retty =
//         translate_ty(ctx, names, body.local_decls[0u32.into()].source_info.span, body.return_ty());

//     Signature {
//         name: format!("promoted{:?}", promoted.as_usize()).into(),
//         attrs: Vec::new(),
//         retty: Some(retty),
//         args,
//         contract: Contract::new(),
//     }
// }

// According to @oli-obk, promoted bodies are:
// > it's completely linear, not even conditions or asserts inside. we should probably document all that with validation
// On this supposition we can simplify the translation *dramatically* and produce why3 constants
// instead of cfgs
//
// We use a custom translation because if we use `any` inside a `constant` / `function` its body is marked as opaque, and `mlcfg` heavily uses `any`.
// pub(crate) fn translate_promoted<'tcx>(
//     ctx: &mut TranslationCtx<'tcx>,
//     names: &mut CloneMap<'tcx>,
//     _: ParamEnv<'tcx>,
//     (promoted, body): (Promoted, &Body<'tcx>),
//     parent: DefId,
// ) -> CreusotResult<Decl> {
//     let mut previous_block = None;
//     let mut exp = Exp::impure_var("_0".into());

//     let func_translator = BodyTranslator::build_context(ctx.tcx, ctx, &body, parent);
//     let fmir = func_translator.translate();

//     for (id, bbd) in fmir.blocks.into_iter().rev() {
//         // Safety check
//         match bbd.terminator {
//             fmir::Terminator::Goto(prev) => {
//                 assert!(previous_block == Some(prev))
//             }
//             fmir::Terminator::Return => {
//                 assert!(previous_block == None);
//             }
//             _ => {}
//         };

//         previous_block = Some(id);

//         let exps: Vec<_> =
//             bbd.stmts.into_iter().map(|s| s.to_why(ctx, names, body)).flatten().collect();
//         exp = exps.into_iter().rfold(exp, |acc, asgn| match asgn {
//             why3::mlcfg::Statement::Assign { lhs, rhs } => {
//                 Exp::Let { pattern: Pattern::VarP(lhs), arg: box rhs, body: box acc }
//             }
//             why3::mlcfg::Statement::Assume(_) => acc,
//             why3::mlcfg::Statement::Invariant(_, _) => todo!(),
//             why3::mlcfg::Statement::Assert(_) => {
//                 ctx.crash_and_error(ctx.def_span(parent), "unsupported promoted constant")
//             }
//         });
//     }
//     let sig = promoted_signature(ctx, names, (promoted, body));
//     Ok(Decl::Let(LetDecl {
//         sig,
//         rec: false,
//         kind: Some(LetKind::Constant),
//         body: exp,
//         ghost: false,
//     }))
// }
