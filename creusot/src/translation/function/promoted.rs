use crate::{
    ctx::{CloneMap, TranslationCtx},
    error::Error,
    translation::{
        binop_to_binop, constant::from_mir_constant, fmir::uint_from_int, function::LocalIdent,
        ty::translate_ty, unop_to_unop,
    },
    util::{self, constructor_qname},
};
use creusot_rustc::{
    middle::{mir::TerminatorKind, ty::ParamEnv},
    smir::mir::{Body, BorrowKind, Operand, Promoted, StatementKind},
};
use why3::{
    declaration::{Contract, Decl, LetDecl, Signature},
    exp::{Binder, Exp, Pattern},
    QName,
};

use crate::error::CreusotResult;

use super::place::translate_rplace_inner;

pub(crate) fn promoted_signature<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    (promoted, body): (Promoted, &Body<'tcx>),
) -> Signature {
    let args = body
        .args_iter()
        .map(|arg| {
            let info = &body.local_decls[arg];
            let ty = translate_ty(ctx, names, info.source_info.span, info.ty);
            Binder::typed(LocalIdent::anon(arg).ident(), ty)
        })
        .collect();
    let retty =
        translate_ty(ctx, names, body.local_decls[0u32.into()].source_info.span, body.return_ty());

    Signature {
        name: format!("promoted{:?}", promoted.as_usize()).into(),
        attrs: Vec::new(),
        retty: Some(retty),
        args,
        contract: Contract::new(),
    }
}

// According to @oli-obk, promoted bodies are:
// > it's completely linear, not even conditions or asserts inside. we should probably document all that with validation
// On this supposition we can simplify the translation *dramatically* and produce why3 constants
// instead of cfgs
//
// We use a custom translation because if we use `any` inside a `constant` / `function` its body is marked as opaque, and `mlcfg` heavily uses `any`.
pub(crate) fn translate_promoted<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    param_env: ParamEnv<'tcx>,
    (promoted, body): (Promoted, &Body<'tcx>),
) -> CreusotResult<Decl> {
    let mut previous_block = None;
    let mut exp = Exp::impure_var("_0".into());
    for (id, bbd) in body.basic_blocks().iter_enumerated().rev() {
        // Safety check
        match bbd.terminator().kind {
            TerminatorKind::Return => {
                assert!(previous_block == None);
            }
            TerminatorKind::Goto { target } => {
                assert!(previous_block == Some(target))
            }
            _ => {}
        }
        previous_block = Some(id);
        use creusot_rustc::{middle::ty::UintTy, smir::mir::Rvalue::*};
        for stmt in bbd.statements.iter().rev() {
            match &stmt.kind {
                StatementKind::Assign(box (tgt, val)) => {
                    let rhs = match val {
                        CopyForDeref(_) => panic!(),
                        Use(op) => translate_operand(ctx, names, body, param_env, op),
                        BinaryOp(op, box (l, r)) | CheckedBinaryOp(op, box (l, r)) => {
                            Exp::BinaryOp(
                                binop_to_binop(ctx, l.ty(body, ctx.tcx), *op),
                                box translate_operand(ctx, names, body, param_env, l),
                                box translate_operand(ctx, names, body, param_env, r),
                            )
                        }
                        Len(pl) => {
                            let int_conversion = uint_from_int(&UintTy::Usize);
                            let len_call = Exp::impure_qvar(
                                QName::from_string("Seq.length").unwrap(),
                            )
                            .app_to(translate_rplace_inner(
                                ctx,
                                names,
                                body,
                                pl.local,
                                pl.projection,
                            ));
                            int_conversion.app_to(len_call)
                        }
                        UnaryOp(op, v) => Exp::UnaryOp(
                            unop_to_unop(*op),
                            box translate_operand(ctx, names, body, param_env, v),
                        ),
                        Aggregate(box kind, ops) => {
                            use creusot_rustc::smir::mir::AggregateKind::*;
                            let fields = ops
                                .iter()
                                .map(|op| translate_operand(ctx, names, body, param_env, op))
                                .collect();

                            match kind {
                                Tuple => Exp::Tuple(fields),
                                Adt(adt, varix, _, _, _) => {
                                    ctx.translate(*adt);
                                    let adt = ctx.adt_def(*adt);
                                    let variant_def = &adt.variants()[*varix];
                                    let qname = constructor_qname(ctx, variant_def);

                                    Exp::Constructor { ctor: qname, args: fields }
                                }
                                Closure(def_id, _)
                                    if util::is_ghost(ctx.tcx, def_id.to_def_id()) =>
                                {
                                    ctx.crash_and_error(
                                        body.span,
                                        "should not have translated ghost closure",
                                    )
                                }
                                _ => ctx.crash_and_error(
                                    stmt.source_info.span,
                                    "unsupported aggregate kind",
                                ),
                            }
                        }
                        Ref(_, BorrowKind::Shared, pl) => {
                            translate_rplace_inner(ctx, names, body, pl.local, pl.projection)
                        }

                        Ref(_, _, _) => Err(Error::new(
                            stmt.source_info.span,
                            "cannot take mutable ref in promoted body",
                        ))?,

                        ShallowInitBox(_, _)
                        | NullaryOp(_, _)
                        | Discriminant(_)
                        | ThreadLocalRef(_)
                        | AddressOf(_, _)
                        | Repeat(_, _)
                        | Cast(_, _, _) => Err(Error::new(
                            stmt.source_info.span,
                            "unsupported rvalue in promoted mir",
                        ))?,
                    };
                    let lhs =
                        LocalIdent::anon(tgt.as_local().ok_or_else(|| {
                            Error::new(stmt.source_info.span, "expected MIR local")
                        })?);
                    exp = Exp::Let {
                        pattern: Pattern::VarP(lhs.ident()),
                        arg: box rhs,
                        body: box exp,
                    };
                }
                _ => Err(Error::new(
                    stmt.source_info.span,
                    "tell Xavier to stop trying to simplify promoted bodies",
                ))?,
            }
        }
    }
    let sig = promoted_signature(ctx, names, (promoted, body));
    Ok(Decl::Let(LetDecl { sig, rec: false, constant: true, body: exp }))
}

fn translate_operand<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    body: &Body<'tcx>,
    param_env: ParamEnv<'tcx>,
    operand: &Operand<'tcx>,
) -> Exp {
    use creusot_rustc::smir::mir::Operand::*;

    match operand {
        Move(pl) | Copy(pl) => translate_rplace_inner(ctx, names, body, pl.local, pl.projection),
        Constant(c) => from_mir_constant(param_env, ctx, c).to_why(ctx, names, Some(body)),
    }
}
