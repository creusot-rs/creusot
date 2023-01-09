use super::{function::LocalIdent, traits};
use crate::{
    backend::clone_map2::{ClosureId, Id},
    ctx::TranslationCtx,
    pearlite::Term,
};
use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{subst::SubstsRef, AdtDef, GenericArg, ParamEnv, Ty, TypeVisitable},
    smir::mir::{BasicBlock, BinOp, UnOp},
    span::{Span, Symbol, DUMMY_SP},
    target::abi::VariantIdx,
};
use indexmap::IndexMap;
use rustc_middle::{
    mir::{tcx::PlaceTy, Local, PlaceElem},
    ty::{List, TyCtxt},
};

#[derive(Clone, Copy, Debug)]
pub struct Place<'tcx> {
    pub local: Local,
    pub ty: Ty<'tcx>,
    pub projection: &'tcx List<PlaceElem<'tcx>>,
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn ty(self, tcx: TyCtxt<'tcx>) -> PlaceTy<'tcx> {
        self.projection
            .iter()
            .fold(PlaceTy::from_ty(self.ty), |acc, elem| acc.projection_ty(tcx, elem))
    }
}

#[derive(Clone)]
pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, RValue<'tcx>),
    // TODO: Remove `Resolve` and replace it with `Assume`.
    // The reason I have not done this yet is that it would require transforming a `Place` to a `Term`.
    Resolve(Id, SubstsRef<'tcx>, Place<'tcx>),
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

#[derive(Clone, Debug)]
pub enum Expr<'tcx> {
    Place(Place<'tcx>),
    Move(Place<'tcx>),
    Copy(Place<'tcx>),
    BinOp(BinOp, Ty<'tcx>, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    UnaryOp(UnOp, Box<Expr<'tcx>>),
    Constructor(DefId, VariantIdx, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
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
) -> Option<(Id, SubstsRef<'tcx>)> {
    if !super::function::resolve_trait_loaded(ctx.tcx) {
        ctx.warn(
            DUMMY_SP,
            "load the `creusot_contract` crate to enable resolution of mutable borrows.",
        );
        return None;
    }

    let trait_meth_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve_method")).unwrap();
    let subst = ctx.mk_substs([GenericArg::from(ty)].iter());

    let (resolve_id, resolve_subst) =
        traits::resolve_opt(ctx.tcx, param_env, trait_meth_id, subst)?;
    // eprintln!("before {:?}", (trait_meth_id, subst));
    // eprintln!("after {:?}", (resolve_id, resolve_subst));

    // eprintln!("{:?} {:?}", ctx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), resolve_id), resolve_subst.type_at(0).is_closure());
    if ctx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), resolve_id)
        && resolve_subst.type_at(0).is_closure()
    {
        return Some((Id(resolve_id, Some(ClosureId::Resolve)), resolve_subst));
    };

    if !ty.still_further_specializable()
        && ctx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), resolve_id)
        && !resolve_subst.type_at(0).is_closure()
    {
        return None;
    }
    eprintln!("resolve {:?}", (resolve_id, resolve_subst));

    Some((resolve_id.into(), resolve_subst))
}
