use crate::{backend::place::projection_ty, pearlite::Term, util::ident_of};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{tcx::PlaceTy, BasicBlock, BinOp, Local, ProjectionElem, UnOp},
    ty::{subst::SubstsRef, AdtDef, Ty, TyCtxt},
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
    Resolve(DefId, SubstsRef<'tcx>, Place<'tcx>),
    Assertion { cond: Term<'tcx>, msg: String },
    AssumeBorrowInv(Place<'tcx>),
    AssertTyInv(Place<'tcx>),
}

// Re-organize this completely
// Get rid of Expr and reimpose a more traditional statement-rvalue-operand setup
#[derive(Clone, Debug)]
pub enum RValue<'tcx> {
    Ghost(Term<'tcx>),
    Borrow(Place<'tcx>),
    /// The source of this borrow is not used after the reborrow, and thus we can
    /// inherit the prophecy identifier.
    ///
    /// The second field is an index in `place.projection`: see
    /// [`NotFinalPlaces::is_final_at`](crate::analysis::NotFinalPlaces::is_final_at).
    FinalBorrow(Place<'tcx>, usize),
    Expr(Expr<'tcx>),
}

#[derive(Clone, Debug)]
pub struct Expr<'tcx> {
    pub kind: ExprKind<'tcx>,
    pub ty: Ty<'tcx>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExprKind<'tcx> {
    // Extract this into a standalone `Operand` type
    Move(Place<'tcx>),
    Copy(Place<'tcx>),
    // Revisit whether this is a good idea to allow general expression trees.
    BinOp(BinOp, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    UnaryOp(UnOp, Box<Expr<'tcx>>),
    Constructor(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    // Should this be a statement?
    Call(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Constant(Term<'tcx>),
    Cast(Box<Expr<'tcx>>, Ty<'tcx>, Ty<'tcx>),
    Tuple(Vec<Expr<'tcx>>),
    Len(Box<Expr<'tcx>>),
    Array(Vec<Expr<'tcx>>),
    Repeat(Box<Expr<'tcx>>, Box<Expr<'tcx>>),
}

impl<'tcx> Expr<'tcx> {
    pub fn is_call(&self) -> bool {
        match &self.kind {
            ExprKind::Move(_) => false,
            ExprKind::Copy(_) => false,
            ExprKind::BinOp(_, _, _) => false,
            ExprKind::UnaryOp(_, _) => false,
            ExprKind::Constructor(_, _, _) => false,
            ExprKind::Call(_, _, _) => true,
            ExprKind::Constant(_) => false,
            ExprKind::Cast(_, _, _) => false,
            ExprKind::Tuple(_) => false,
            ExprKind::Len(_) => false,
            ExprKind::Array(_) => false,
            ExprKind::Repeat(_, _) => false,
        }
    }

    pub fn is_pure(&self) -> bool {
        match &self.kind {
            ExprKind::Move(_) => true,
            ExprKind::Copy(_) => true,
            ExprKind::BinOp(
                BinOp::Add | BinOp::Mul | BinOp::Rem | BinOp::Div | BinOp::Sub,
                _,
                _,
            ) => false,
            ExprKind::BinOp(_, _, _) => true,
            ExprKind::UnaryOp(UnOp::Neg, _) => false,
            ExprKind::UnaryOp(_, _) => true,
            ExprKind::Constructor(_, _, es) => es.iter().all(|e| e.is_pure()),
            ExprKind::Call(_, _, es) => es.iter().all(|e| e.is_pure()),
            ExprKind::Constant(_) => true,
            ExprKind::Cast(_, _, _) => false,
            ExprKind::Tuple(es) => es.iter().all(|e| e.is_pure()),
            ExprKind::Len(e) => e.is_pure(),
            ExprKind::Array(es) => es.iter().all(|e| e.is_pure()),
            ExprKind::Repeat(l, r) => l.is_pure() && r.is_pure(),
        }
    }
}

#[derive(Clone)]
pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(Expr<'tcx>, Branches<'tcx>),
    Return,
    Abort(Span),
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
