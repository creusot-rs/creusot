use super::{function::LocalIdent, traits};
use crate::{ctx::TranslationCtx, pearlite::Term};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{subst::SubstsRef, AdtDef, GenericArg, ParamEnv, Ty, TypeVisitable};
use rustc_smir::mir::{BasicBlock, BinOp, Place, UnOp};
use rustc_span::{Span, Symbol, DUMMY_SP};
use rustc_target::abi::VariantIdx;

#[derive(Clone)]
pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, RValue<'tcx>),
    // TODO: Remove `Resolve` and replace it with `Assume`.
    // The reason I have not done this yet is that it would require transforming a `Place` to a `Term`.
    Resolve(DefId, SubstsRef<'tcx>, Place<'tcx>),
    Assertion(Term<'tcx>),
    Invariant(Symbol, Term<'tcx>),
}

// Re-organize this completely
// Get rid of Expr and reimpose a more traditional statement-rvalue-operand setup
#[derive(Clone)]
pub enum RValue<'tcx> {
    Ghost(Term<'tcx>),
    Borrow(Place<'tcx>),
    Expr(Expr<'tcx>),
}

#[derive(Clone)]
pub enum Expr<'tcx> {
    Place(Place<'tcx>),
    Move(Place<'tcx>),
    Copy(Place<'tcx>),
    BinOp(BinOp, Ty<'tcx>, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    UnaryOp(UnOp, Box<Expr<'tcx>>),
    Constructor(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    // Should this be a statement?
    Call(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Constant(Term<'tcx>),
    Cast(Box<Expr<'tcx>>, Ty<'tcx>, Ty<'tcx>),
    Tuple(Vec<Expr<'tcx>>),
    Span(Span, Box<Expr<'tcx>>),
    Len(Box<Expr<'tcx>>),
}

#[derive(Clone)]
pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(Expr<'tcx>, Branches<'tcx>),
    Return,
    Abort,
}

#[derive(Clone)]
pub enum Branches<'tcx> {
    Int(Vec<(i128, BasicBlock)>, BasicBlock),
    Uint(Vec<(u128, BasicBlock)>, BasicBlock),
    Constructor(AdtDef<'tcx>, SubstsRef<'tcx>, Vec<(VariantIdx, BasicBlock)>, BasicBlock),
    Bool(BasicBlock, BasicBlock),
}

#[derive(Clone)]
pub struct Block<'tcx> {
    pub(crate) stmts: Vec<Statement<'tcx>>,
    pub(crate) terminator: Terminator<'tcx>,
}

#[derive(Clone)]
pub struct Body<'tcx> {
    // TODO: Split into return local, args, and true locals?
    // TODO: Remove usage of `LocalIdent`.
    pub(crate) locals: Vec<(LocalIdent, Span, Ty<'tcx>)>,
    pub(crate) arg_count: usize,
    pub(crate) blocks: IndexMap<BasicBlock, Block<'tcx>>,
}

pub(crate) fn resolve_predicate_of2<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    if !super::function::resolve_trait_loaded(ctx.tcx) {
        ctx.warn(
            DUMMY_SP,
            "load the `creusot_contract` crate to enable resolution of mutable borrows.",
        );
        return None;
    }

    let trait_meth_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve_method")).unwrap();
    let subst = ctx.mk_substs([GenericArg::from(ty)].iter());

    let resolve_impl = traits::resolve_opt(ctx.tcx, param_env, trait_meth_id, subst)?;

    if !ty.still_further_specializable()
        && ctx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), resolve_impl.0)
        && !resolve_impl.1.type_at(0).is_closure()
    {
        return None;
    }

    Some(resolve_impl)
}
