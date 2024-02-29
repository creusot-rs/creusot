use crate::{backend::place::projection_ty, pearlite::Term, util::ident_of};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{tcx::PlaceTy, BasicBlock, BinOp, Local, ProjectionElem, UnOp},
    ty::{AdtDef, GenericArgsRef, Ty, TyCtxt},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::VariantIdx;

pub use rustc_span::DUMMY_SP;

#[derive(Clone, Debug)]
pub struct Place<'tcx> {
    pub(crate) local: Symbol,
    pub(crate) projection: Vec<ProjectionElem<Symbol, Ty<'tcx>>>,
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> Ty<'tcx> {
        let mut ty = PlaceTy::from_ty(locals[&self.local].ty);

        for p in &self.projection {
            ty = projection_ty(ty, tcx, *p);
        }

        ty.ty
    }

    pub(crate) fn as_symbol(&self) -> Option<Symbol> {
        if self.projection.is_empty() {
            Some(self.local)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, RValue<'tcx>, Span),
    Resolve(DefId, GenericArgsRef<'tcx>, Place<'tcx>),
    Assertion { cond: Term<'tcx>, msg: String },
    AssumeBorrowInv(Place<'tcx>),
    // Todo: fold into `Assertion`
    AssertTyInv(Place<'tcx>),
    Call(Place<'tcx>, DefId, GenericArgsRef<'tcx>, Vec<Operand<'tcx>>, Span),
}

// TODO: Add shared borrows?
#[derive(Clone, Copy, Debug)]
pub enum BorrowKind {
    /// Ordinary mutable borrows
    Mut,
    /// The source of this borrow is not used after the reborrow, and thus we can
    /// inherit the prophecy identifier.
    ///
    /// The second field is an index in `place.projection`: see
    /// [`NotFinalPlaces::is_final_at`](crate::analysis::NotFinalPlaces::is_final_at).
    Final(usize),
}

#[derive(Clone, Debug)]
pub enum RValue<'tcx> {
    Ghost(Term<'tcx>),
    Borrow(BorrowKind, Place<'tcx>),
    Expr(Expr<'tcx>),
}

// TODO Inline `Expr` in to `RValue`
#[derive(Clone, Debug)]
pub struct Expr<'tcx> {
    pub kind: ExprKind<'tcx>,
    pub ty: Ty<'tcx>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Operand<'tcx> {
    Move(Place<'tcx>),
    Copy(Place<'tcx>),
    Constant(Term<'tcx>),
}

impl<'tcx> Operand<'tcx> {
    pub fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> Ty<'tcx> {
        match self {
            Operand::Move(pl) => pl.ty(tcx, locals),
            Operand::Copy(pl) => pl.ty(tcx, locals),
            Operand::Constant(t) => t.ty,
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExprKind<'tcx> {
    Operand(Operand<'tcx>),
    // Revisit whether this is a good idea to allow general expression trees.
    BinOp(BinOp, Operand<'tcx>, Operand<'tcx>),
    UnaryOp(UnOp, Operand<'tcx>),
    Constructor(DefId, GenericArgsRef<'tcx>, Vec<Operand<'tcx>>),
    Cast(Operand<'tcx>, Ty<'tcx>, Ty<'tcx>),
    Tuple(Vec<Operand<'tcx>>),
    Len(Operand<'tcx>),
    Array(Vec<Operand<'tcx>>),
    Repeat(Operand<'tcx>, Operand<'tcx>),
}

impl<'tcx> Expr<'tcx> {
    pub fn is_call(&self) -> bool {
        match &self.kind {
            ExprKind::Operand(_) => false,
            ExprKind::BinOp(_, _, _) => false,
            ExprKind::UnaryOp(_, _) => false,
            ExprKind::Constructor(_, _, _) => false,
            ExprKind::Cast(_, _, _) => false,
            ExprKind::Tuple(_) => false,
            ExprKind::Len(_) => false,
            ExprKind::Array(_) => false,
            ExprKind::Repeat(_, _) => false,
        }
    }

    pub fn is_pure(&self) -> bool {
        match &self.kind {
            ExprKind::Operand(_) => true,
            ExprKind::BinOp(
                BinOp::Add | BinOp::Mul | BinOp::Rem | BinOp::Div | BinOp::Sub,
                _,
                _,
            ) => false,
            ExprKind::BinOp(_, _, _) => true,
            ExprKind::UnaryOp(UnOp::Neg, _) => false,
            ExprKind::UnaryOp(_, _) => true,
            ExprKind::Constructor(_, _, _) => true,
            ExprKind::Cast(_, _, _) => false,
            ExprKind::Tuple(_) => true,
            ExprKind::Len(_) => true,
            ExprKind::Array(_) => true,
            ExprKind::Repeat(_, _) => true,
        }
    }
}

#[derive(Clone)]
pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(self::Operand<'tcx>, Branches<'tcx>),
    Return,
    Abort(Span),
}

impl<'tcx> Terminator<'tcx> {
    pub fn targets(&self) -> impl Iterator<Item = BasicBlock> + '_ {
        use std::iter::*;
        match self {
            Terminator::Goto(bb) => Box::new(once(*bb)) as Box<dyn Iterator<Item = BasicBlock>>,
            Terminator::Switch(_, brs) => match brs {
                Branches::Int(brs, def) => Box::new(brs.iter().map(|(_, b)| *b).chain(once(*def)))
                    as Box<dyn Iterator<Item = BasicBlock>>,
                Branches::Uint(brs, def) => Box::new(brs.iter().map(|(_, b)| *b).chain(once(*def)))
                    as Box<dyn Iterator<Item = BasicBlock>>,
                Branches::Constructor(_, _, brs, def) => {
                    Box::new(brs.iter().map(|(_, b)| *b).chain(once(*def)))
                        as Box<dyn Iterator<Item = BasicBlock>>
                }
                Branches::Bool(f, t) => {
                    Box::new([*f, *t].into_iter()) as Box<dyn Iterator<Item = BasicBlock>>
                }
            },
            Terminator::Return => Box::new(empty()) as Box<dyn Iterator<Item = BasicBlock>>,
            Terminator::Abort(_) => Box::new(empty()) as Box<dyn Iterator<Item = BasicBlock>>,
        }
    }
}

#[derive(Clone)]
pub enum Branches<'tcx> {
    Int(Vec<(i128, BasicBlock)>, BasicBlock),
    Uint(Vec<(u128, BasicBlock)>, BasicBlock),
    Constructor(AdtDef<'tcx>, GenericArgsRef<'tcx>, Vec<(VariantIdx, BasicBlock)>, BasicBlock),
    Bool(BasicBlock, BasicBlock),
}

#[derive(Clone)]
pub struct Block<'tcx> {
    pub(crate) invariants: Vec<Term<'tcx>>,
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) stmts: Vec<Statement<'tcx>>,
    pub(crate) terminator: Terminator<'tcx>,
}

/// A MIR local along with an optional human-readable name
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum LocalIdent {
    Anon(Local),
    User(Symbol),
}

impl LocalIdent {
    pub(crate) fn anon(loc: Local) -> Self {
        LocalIdent::Anon(loc)
    }

    pub(crate) fn dbg_raw(_: Local, name: Symbol) -> Self {
        LocalIdent::User(name)
    }

    pub(crate) fn symbol(&self) -> Symbol {
        match &self {
            LocalIdent::User(id) => Symbol::intern(&format!("{}", &*ident_of(*id))),
            LocalIdent::Anon(loc) => Symbol::intern(&format!("_{}", loc.index())),
        }
    }

    pub(crate) fn is_anon(&self) -> bool {
        matches!(self, LocalIdent::Anon(_))
    }
}

pub type LocalDecls<'tcx> = IndexMap<Symbol, LocalDecl<'tcx>>;

#[derive(Clone, Debug)]
pub struct LocalDecl<'tcx> {
    // Original MIR local
    pub(crate) mir_local: Local,
    pub(crate) span: Span,
    pub(crate) ty: Ty<'tcx>,
    // Is this a MIR temporary?
    pub(crate) temp: bool,
    // Is this declaration a function argument or return place?
    pub(crate) arg: bool,
}

#[derive(Clone)]
pub struct Body<'tcx> {
    // TODO: Split into return local, args, and true locals?
    // TODO: Remove usage of `LocalIdent`.
    pub(crate) locals: LocalDecls<'tcx>,
    pub(crate) arg_count: usize,
    pub(crate) blocks: IndexMap<BasicBlock, Block<'tcx>>,
}
