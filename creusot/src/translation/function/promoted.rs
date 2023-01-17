// use crate::{
//     ctx::{CloneMap, TranslationCtx},
//     translation::{fmir, function::LocalIdent, ty::translate_ty},
// };
// use rustc_hir::def_id::DefId;
// use rustc_middle::{
//     mir::{Body, Promoted},
//     ty::ParamEnv,
// };
// use why3::{
//     declaration::{Contract, Decl, LetDecl, LetKind, Signature},
//     exp::{Binder, Exp, Pattern},
// };

// use crate::error::CreusotResult;

// use super::BodyTranslator;

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

// // According to @oli-obk, promoted bodies are:
// // > it's completely linear, not even conditions or asserts inside. we should probably document all that with validation
// // On this supposition we can simplify the translation *dramatically* and produce why3 constants
// // instead of cfgs
// //
// // We use a custom translation because if we use `any` inside a `constant` / `function` its body is marked as opaque, and `mlcfg` heavily uses `any`.
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
